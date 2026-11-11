-- Prove2me | Theorems.Thm_WeakStrongMSR_theorem_1_2
-- name    : WeakStrongMSR.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:56.942967+00:00
-- url     : https://prove2.me/theorems/946d90ac-7553-4f50-94cc-0a52d4cf86ec
-- title:
--   Theorem 1.2 — a polynomial-time $O(1)$-approximation for MSR with $O(k\log n\log\log n/(1/2-\delta)^3)$ strong queries, for every $\delta<1/2$
-- statement:
--   Let $\delta\in(0,\tfrac12)$, let $(X,d)$ be a metric on $n$ points with a known bound $\Delta\le n^{O(1)}$ on its aspect ratio, and let $k\ge1$. Weak distances are corrupted independently with probability $\delta$, and an adversary that knows $d$ and the corrupted set chooses the corrupted values. $\mathrm{OPT}$ is the minimum sum of radii of at most $k$ balls covering $X$.
--
--   There is a single program $P$ of the weak–strong real RAM, which receives $n,k,\delta,\Delta$ and accesses $d$ only through weak reads (free) and strong queries (counted). There are also constants $C_{\mathrm{apx}}$ and $a>0$. For every exponent $e$ there are $C_q$ and $n_0$, and for every $\delta\in(0,\tfrac12)$ there are $C_t$ and $b$, such that the following holds for all $n\ge n_0$, all $k\ge1$, all metrics $d$, all $\Delta$ with $\mathrm{aspect}(d)\le\Delta\le n^e$ and every adversary.
--
--   1. On every corruption set and every random tape, $P$ halts within $\lfloor C_tn^b\rfloor$ steps with a $k$-slot solution at its output addresses, after at most
--   $$C_q\,\frac{k\log n\,\log\log n}{(\tfrac12-\delta)^3}$$
--   strong queries.
--   2. The event that the output is valid (every point lies in the ball of its slot) and has total radius at most $C_{\mathrm{apx}}\cdot\mathrm{OPT}$ is measurable in the tape. Its probability over the corruption set and the tape is at least $1-n^{-a}$.
--
--   The approximation constant $C_{\mathrm{apx}}$ and the exponent $a$ do not depend on $\delta$ or $e$, and $C_q$ does not depend on $\delta$. This is the main result of the paper.
--
--   **Formalization Note** $\mathrm{OPT}$ is the published `msrOpt`. The logarithm is natural. The machine is `WeakStrongMSR.Machine`: its input never contains $d$, and exact distances are available only between strongly queried points.
--
--   Differences from the source:
--   - reading: "polynomial-time algorithm" → one admissible program of the weak–strong randomized real RAM (unit-cost steps, free weak reads, every strong execution counted, exact distances only between strongly queried points) halting within ⌊C_t n^b⌋ steps; reason: the paper names no machine; the real RAM is the natural model for real inputs and has no floor, log or exp, so fewer algorithms qualify
--   - reading: "Let δ be a constant … there is an algorithm … The approximation factor does not depend on δ" → one program for every δ (δ is an input); C_apx and a chosen before e and δ; C_q before δ; C_t, b after δ; reason: App. A: "The algorithm knows δ"; c does not depend on δ; the query bound is O(kh/γ) per test with an absolute constant
--   - reading: queries O(·) and polynomial time → bounds on every run: every corruption set, every adversary and every tape; reason: Lemma 3.34 ("including if it aborts") and Lemma 3.37 ("on every run")
--   - generalization: tapes of uniform [0,1] reals → the resource bounds and well-formed output hold for every tape ω : ℕ → ℝ; reason: more tapes; specializes to [0,1]-valued tapes
--   - reading: "with high probability"; "Δ ≤ n^{O(1)}" → probability ≥ 1 − n^{−a}, a > 0 absolute, for n ≥ n₀; for every exponent e with aspect(d) ≤ Δ ≤ n^e (C_q, n₀ depend on e); reason: §2.3 definitions of whp and of the known aspect-ratio bound
--   - encoding: corrupted pairs, adversary knowing d and Corrupt → independent Bernoulli(δ) corruption of each pair (exact δ); adversary a function of the corruption set, quantified after d; reason: Def. 1.1, §2.2, §4 ("exactly δ"); a randomized adversary is a mixture of these
--   - encoding: at most k balls and an assignment → k slots (centre, radius) and a slot label per point; empty slots allowed; reason: same solutions as "at most k balls"
--   - encoding: OPT, log → OPT = MinSumRadiiPTAS.Main.msrOpt d k; natural logarithm; reason: msrOpt equals the paper's OPT for k ≥ 1; the base of log is absorbed in the constants
--   - encoding: the success probability → the success event is also asserted measurable in the tape; reason: needed for the probability to be the measure of the event; it holds for every program on this machine
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), Theorem 1.2, p.2 (PDF 3); Theorem A.1, p.35 (PDF 36); §2.3, p.5

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Machine

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-- **Theorem 1.2** (Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong
and Weak Oracles*, manuscript, sha256 5f8fbaf3…67e8f92a0, p.2; proved as Theorem A.1, p.35).
"Let δ ∈ (0, 1/2) be a constant. There is a polynomial-time algorithm that makes
O(k log n log log n/(1/2 − δ)³) strong point queries, and with high probability returns at most k
balls and an assignment of every point to a returned ball that contains it, of total radius
O(OPT). The approximation factor does not depend on δ."

There is one admissible program `P` of the weak–strong real RAM, an approximation constant `Capx`
and a failure exponent `a > 0`, such that for every aspect-ratio exponent `e` there are `Cq` and
`n₀`, and for every `δ ∈ (0, 1/2)` there are `Ct` and `b`, with: for every `n ≥ n₀`, `k ≥ 1`,
metric `d` on `Fin n`, aspect-ratio bound `Δ` with `aspect(d) ≤ Δ ≤ n^e`, and adversary `adv`,
writing `T = ⌊Ct n^b⌋`,
1. on every corruption set and every tape, after `T` steps the run has halted with a solution at
   the output addresses and has made at most `Cq k log n log log n/(1/2 − δ)³` strong queries;
2. the set of tapes on which the output is a valid solution of total radius `≤ Capx · OPT` is
   measurable, and its probability over the corruption set and the tape is at least `1 − n^{−a}`.

**Formalization Note.** The machine is `WeakStrongMSR.Machine` (weak reads free, every `strong`
execution counted, exact distances only between strongly queried points; the input holds
`n, k, δ, Δ` and never `d`). `OPT` is the published `MinSumRadiiPTAS.Main.msrOpt d k`. The logarithm
is natural. `Capx` and `a` are chosen before `e` and `δ` ("the approximation factor does not depend
on δ"; App. A: every bound fails with probability `n^{−Ω(c)}`); `Cq` depends only on `e`; the
running-time constants may depend on `e` and `δ`. -/
theorem theorem_1_2 :
    ∃ P : Program, Admissible P ∧ ∃ Capx a : ℝ, 0 < a ∧
    ∀ e : ℕ, ∃ (Cq : ℝ) (n₀ : ℕ),
    ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∃ (Ct : ℝ) (b : ℕ),
    ∀ n : ℕ, n₀ ≤ n → ∀ k : ℕ, 1 ≤ k →
    ∀ d : Fin n → Fin n → ℝ, MinSumClust.IsMetric d →
    ∀ Δ : ℝ, aspectRatio d ≤ Δ → Δ ≤ (n : ℝ) ^ e → ∀ adv : Adversary n,
      (∀ C ⊆ pairs n, ∀ ω : ℕ → ℝ,
        (∃ (σ : Fin n → Fin k) (ctr : Fin k → Fin n) (rad : Fin k → ℝ), OutputsSolution
          (run P n k δ Δ (weakDist d C adv) d ω ⌊Ct * (n : ℝ) ^ b⌋₊) σ ctr rad) ∧
        ((run P n k δ Δ (weakDist d C adv) d ω ⌊Ct * (n : ℝ) ^ b⌋₊).queries : ℝ) ≤
          Cq * k * Real.log n * Real.log (Real.log n) / (1 / 2 - δ) ^ 3) ∧
      (∀ C ⊆ pairs n, MeasurableSet {ω : ℕ → ℝ | ∃ (σ : Fin n → Fin k) (ctr : Fin k → Fin n) (rad : Fin k → ℝ),
          OutputsSolution (run P n k δ Δ (weakDist d C adv) d ω ⌊Ct * (n : ℝ) ^ b⌋₊) σ ctr rad ∧
          ValidSolution d σ ctr rad ∧ solCost rad ≤ Capx * MinSumRadiiPTAS.Main.msrOpt d k}) ∧
      ENNReal.ofReal (1 - (n : ℝ) ^ (-a)) ≤
        ∑ C ∈ (pairs n).powerset, ENNReal.ofReal (corrWeight δ C) *
          MinSumFPT.tapeLaw {ω : ℕ → ℝ | ∃ (σ : Fin n → Fin k) (ctr : Fin k → Fin n) (rad : Fin k → ℝ),
            OutputsSolution (run P n k δ Δ (weakDist d C adv) d ω ⌊Ct * (n : ℝ) ^ b⌋₊) σ ctr rad ∧
            ValidSolution d σ ctr rad ∧ solCost rad ≤ Capx * MinSumRadiiPTAS.Main.msrOpt d k} := by sorry

end WeakStrongMSR
