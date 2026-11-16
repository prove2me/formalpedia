-- Prove2me | Theorems.Thm_QMCBeyondHK_Supplement_theorem_1_3
-- name    : QMCBeyondHK.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:17:03.684533+00:00
-- url     : https://prove2.me/theorems/134faaca-b1fd-42e1-ba49-0124cb396b9c
-- title:
--   Theorem 1.3 — a linear-feedback Haar-thinning point sequence keeps $n$ of $(1+\varepsilon)n$ samples with star discrepancy $D^\star \le O_{d,\varepsilon}(\log^{d+1} n)$ w.h.p.
-- statement:
--   There is an absolute constant $c > 0$ such that the following holds. For every dimension $d \ge 1$, every $\varepsilon \in (0,1)$ and every $k \ge 1$ there are constants $\kappa > 0$, $C_B > 0$ and $C$, and schedules $\ell_s : \mathbb N \to \mathbb N$, $B_s : \mathbb N \to \mathbb R$ with
--   $$
--   \ell_s(t) \le \lceil \kappa \log_2((t+1)d) \rceil, \qquad 0 < B_s(t) \le C_B\,(1 + \log_2(t+1))^{d+1} \quad (t \ge 0),
--   $$
--   all depending only on $d$, $\varepsilon$ and $k$ (not on $n$), such that the linear-feedback Haar-thinning algorithm of Section 4.1, run on independent inputs $x_t, y_t \sim \mathrm{Unif}[0,1)^d$, $\xi_t \sim \mathrm{Unif}[0,1)$ with level $\ell_s(t)$ and threshold $B_s(t)$ at step $t$, satisfies for every $n \ge 1$, with $A = (z_0, \dots, z_{n-1})$ its first $n$ retained points:
--
--   1. **Low star discrepancy w.h.p.** With probability at least $1 - (nd)^{-k}$, the algorithm does not FAIL at any step $t < n$ and
--   $$
--   D^\star(A) \le C\,(1 + \log_2 n)^{d+1}.
--   $$
--   2. **$(1+\varepsilon)n$ samples.** The probability that the algorithm does not FAIL before step $n$ and uses more than $(1+\varepsilon)n$ samples in its first $n$ steps is at most $\exp(-c\varepsilon n)$.
--   3. **Online, no two consecutive discards.** The point retained at step $t$ is $x_t$ if $x_t$ is accepted and the fresh sample $y_t$ otherwise; the acceptance decision and the retained point depend only on the inputs of steps $0, \dots, t$.
--   4. **Per-sample work.** At step $t$, with $\ell = \ell_s(t)$, at every $x \in [0,1)^d$ at most $N_\ell = (\ell+1)^d$ Haar functions of $\Pi_{\le\ell}$ are nonzero, so $\Phi_t(x)$ is a sum of at most $N_\ell$ nonzero terms, and step $t$ changes $\varphi$ only at the Haar functions that are nonzero at $z_t$. Since $\ell_s(t) = O(\log(td))$, this is $\widetilde O_{d,\varepsilon}(1)$ work per sample.
--
--   Because the schedules are fixed before $n$, the retained points form one point sequence whose every prefix has star discrepancy $O_{d,\varepsilon}(\log^{d+1} n)$ with high probability (footnote 2: a point sequence is required to have small star discrepancy for every $n$ simultaneously). This is the paper's second main result. It improves the $O_{d,\varepsilon}(\log^{2d+1} n)$ star discrepancy of the Haar-thinning strategy of Dwivedi, Feldheim, Gurel-Gurevich and Ramdas to the $O_{d,\varepsilon}(\log^{d+1} n)$ bound they conjectured, within one $\log n$ factor of the best explicit point sequences.
--
--   **Formalization Note** Section 4.1 describes the algorithm for a given $n$ (constant level $\ell = O(\log(nd))$ and threshold $B = O_{d,\varepsilon}(\log^{d+1} n)$); footnote 9 says the point sequence "as stated in Theorem 1.3" is produced by making the parameters step-dependent as in footnote 7, without fixing the schedule, so the schedule is existential within these growth rates. "With high probability" is the paper's $1 - 1/\mathrm{poly}(nd)$ for an arbitrary polynomial (Lemmas 4.6.1 and 4.6.2, by choosing the constant in $B$), pinned as $(nd)^{-k}$ for every $k$; $O_{d,\varepsilon}(\log^{d+1} n)$ is pinned as $C(1+\log_2 n)^{d+1}$. The inputs are an unbounded independent uniform stream on an arbitrary probability space (`QMCBeyondHK.IsStreamInput`). Probabilities are measures of sets of outcomes in $[0,\infty]$.
--
--   Differences from the source:
--   - reading: there is a randomized algorithm → the linear-feedback Haar-thinning algorithm of §4.1 with step-dependent level ℓs t ≤ ⌈κ log₂((t+1)d)⌉ and threshold 0 < Bs t ≤ C_B(1 + log₂(t+1))^{d+1}, the schedules existential (fixed before n); reason: §4 constructs and analyzes this algorithm and footnote 9 (p.16) obtains the point sequence of the theorem by making its parameters step-dependent as in footnote 7 (p.8), without fixing the schedule; an existential over unrestricted algorithms would be trivialized
--   - reading: low-discrepancy point sequences (title; footnote 9: "a point sequence as stated in Theorem 1.3"), given n ∈ Z>0 → one algorithm, independent of n, whose first n retained points satisfy the bounds for every n ≥ 1; reason: footnote 2 (p.1) defines a point sequence as one whose first n points have small star discrepancy for every n, and calls the point-set notion strictly weaker; the per-n probability bound is the "with high probability" of the statement
--   - reading: with high probability, D⋆(A) ≤ O_{d,ε}(log^{d+1} n) → for every k ≥ 1 there are κ, C_B, C and schedules depending on d, ε, k with P(FAIL at some t < n, or D⋆(A) > C(1 + log₂ n)^{d+1}) ≤ (nd)^{−k}; reason: Lemmas 4.6.1–4.6.2 prove 1 − 1/poly(nd) for an arbitrary polynomial by taking the constant in B large; the algorithm returns no valid output after a FAIL, so FAIL counts as failure
--   - reading: log^{d+1} n → (1 + log₂ n)^{d+1}; reason: log^{d+1} 1 = 0 while a one-point set has positive star discrepancy, so the literal bound is false at n = 1; for n ≥ 2 the two differ by a factor at most 2^{d+1}, absorbed in O_{d,ε}
--   - reading: takes as input (1 + ε)n i.i.d. uniform samples → the algorithm reads an unbounded independent uniform stream and, with probability at most exp(−cεn), c absolute, does not FAIL before step n and consumes more than (1 + ε)n samples in its first n steps; reason: Proposition 2.4 applies while μ_t is a valid thinning density, i.e. before a FAIL; the FAIL event is bounded in clause 1
--   - reading: the algorithm is online and never discards two consecutive samples → the retained point at step t is x_t if accepted and y_t otherwise, and the decision and retained point depend only on the inputs of steps ≤ t; reason: the structural properties of the thinning framework (§2.1, p.7)
--   - reading: spends Õ_{d,ε}(1) time to process each sample → at step t at most N_ℓ = (ℓ + 1)^d functions of Π≤ℓ, ℓ = ℓs t, are nonzero at any point, and a step changes φ only at the Haar functions nonzero at z_t; reason: the paper has no machine model; with ℓs t = O(log(td)) this term count is Õ_{d,ε}(1)
--   - generalization: the algorithm's own i.i.d. uniform samples and coins → any probability space carrying a measurable independent uniform input stream (IsStreamInput); reason: the canonical product space is one such space; every statement about the law of the run specializes to it
--   - encoding: a finite point set A and |A ∩ R| → a tuple Fin n → [0,1)^d counted with multiplicity, D_R(A) = (number of t with A t ∈ R) − n·vol(R) with vol as a real number; reason: the output of n thinning steps is an n-tuple; same instances
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), Theorem 1.3, p.3 (PDF p.5), restated p.15 (PDF p.17); algorithm §4.1, p.16 (PDF p.18); proof §4.2–4.3, pp.17–20 (PDF pp.19–22)

import Mathlib
import Definitions.Def_QMCBeyondHK_IsStreamInput
import Definitions.Def_QMCBeyondHK_Supplement_starDisc
import Definitions.Def_QMCBeyondHK_Supplement_lfRun

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QMCBeyondHK.Supplement

/-- Theorem 1.3 (Low-discrepancy point sequences via `(1 + ε)n` samples), printed p.3 (PDF p.5;
restated p.15, PDF p.17) of Ezeunala, Jha, Jiang, arXiv:2609.10921 (sha256 bc273e88…), for the
point-sequence version of linear-feedback Haar-thinning (§4.1 with footnotes 7 and 9): the
algorithm of §4.1 whose level and threshold at step `t` are `ℓs t ≤ ⌈κ log₂((t+1)d)⌉` and
`0 < Bs t ≤ C_B (1 + log₂(t+1))^{d+1}`. There is an absolute `c > 0`, and for every `d ≥ 1`,
`ε ∈ (0,1)` and `k ≥ 1` there are constants `κ, C_B > 0`, `C` and schedules `ℓs, Bs` as above
(depending on `d, ε, k` only, not on `n`) such that for every `n ≥ 1`, with `A` the first `n`
retained points:
(a) with probability at least `1 − (nd)^{−k}` the algorithm does not FAIL at any step `t < n`
and `D⋆(A) ≤ C (1 + log₂ n)^{d+1}`;
(b) with probability at most `exp(−cεn)` it does not FAIL before step `n` and uses more than
`(1 + ε)n` samples in its first `n` steps;
(c) it retains `x_t` when it accepts and `y_t` otherwise, so it never discards two consecutive
samples, and step `t` depends only on the inputs of steps `≤ t` (online);
(d) at every point at most `N_ℓ = (ℓ+1)^d`, `ℓ = ℓs t`, Haar functions of `Π≤ℓ` are nonzero, so
`Φ_t(x)` is a sum of at most `N_ℓ` nonzero terms, and a step changes `φ` only at the Haar
functions nonzero at `z_t`.

**Formalization Note** "Point sequence" (footnote 2, p.1: the first `n` points have small star
discrepancy for every `n`) is encoded by schedules fixed before `n`; footnote 9 (p.16) says the
sequence is obtained by making the parameters step-dependent as in footnote 7, without fixing
the schedule, so the schedule is existential within the paper's growth rates `ℓ = O(log(td))`,
`B = O_{d,ε}(log^{d+1} t)`. "With high probability" is the paper's `1 − 1/poly(nd)` for an
arbitrary polynomial (Lemmas 4.6.1–4.6.2), pinned as `(nd)^{−k}` for every `k`;
`O_{d,ε}(log^{d+1} n)` is pinned as `C (1 + log₂ n)^{d+1}`. The algorithm reads an unbounded
independent uniform stream. "Õ_{d,ε}(1) time per sample" is the term count (d), with
`ℓs t = O(log(td))`. -/
theorem theorem_1_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 1 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ k : ℕ, 1 ≤ k →
    ∃ κ C_B C : ℝ, 0 < κ ∧ 0 < C_B ∧ ∃ ℓs : ℕ → ℕ, ∃ Bs : ℕ → ℝ,
    (∀ t : ℕ, ℓs t ≤ lfLevel κ (t + 1) d ∧ 0 < Bs t ∧ Bs t ≤ lfBudget C_B d (t + 1)) ∧
    ∀ n : ℕ, 1 ≤ n →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : ℕ → Ω → Fin d → ℝ) (Ξ : ℕ → Ω → ℝ) (Y : ℕ → Ω → Fin d → ℝ),
      IsStreamInput P X Ξ Y →
      P {ω | (∃ t < n, FailsAt d (Bs t) (ℓs t) (lfRun d ε ℓs Bs (X · ω) (Ξ · ω) (Y · ω) t)) ∨
          C * (1 + Real.logb 2 n) ^ (d + 1)
            < starDisc (lfOutput d ε ℓs Bs n (X · ω) (Ξ · ω) (Y · ω))}
          ≤ ENNReal.ofReal (1 / ((n : ℝ) * d) ^ k) ∧
      P {ω | (∀ t < n, ¬ FailsAt d (Bs t) (ℓs t) (lfRun d ε ℓs Bs (X · ω) (Ξ · ω) (Y · ω) t)) ∧
          (1 + ε) * (n : ℝ) < (lfNumSamples d ε ℓs Bs n (X · ω) (Ξ · ω) (Y · ω) : ℝ)}
          ≤ ENNReal.ofReal (Real.exp (-(c * ε * n))) ∧
      (∀ ω, ∀ t : ℕ,
        (LFAccepts d ε (Bs t) (ℓs t) (lfRun d ε ℓs Bs (X · ω) (Ξ · ω) (Y · ω) t) (X t ω) (Ξ t ω) →
          lfPoint d ε ℓs Bs (X · ω) (Ξ · ω) (Y · ω) t = X t ω) ∧
        (¬ LFAccepts d ε (Bs t) (ℓs t) (lfRun d ε ℓs Bs (X · ω) (Ξ · ω) (Y · ω) t) (X t ω) (Ξ t ω) →
          lfPoint d ε ℓs Bs (X · ω) (Ξ · ω) (Y · ω) t = Y t ω)) ∧
      (∀ ω ω', ∀ t : ℕ,
        (∀ u : ℕ, u ≤ t → X u ω = X u ω' ∧ Ξ u ω = Ξ u ω' ∧ Y u ω = Y u ω') →
        (LFAccepts d ε (Bs t) (ℓs t) (lfRun d ε ℓs Bs (X · ω) (Ξ · ω) (Y · ω) t) (X t ω) (Ξ t ω) ↔
          LFAccepts d ε (Bs t) (ℓs t) (lfRun d ε ℓs Bs (X · ω') (Ξ · ω') (Y · ω') t) (X t ω')
            (Ξ t ω')) ∧
        lfPoint d ε ℓs Bs (X · ω) (Ξ · ω) (Y · ω) t
          = lfPoint d ε ℓs Bs (X · ω') (Ξ · ω') (Y · ω') t) ∧
      (∀ t : ℕ, ∀ x ∈ cube d,
        ((lowOrder d (ℓs t)).filter (fun H => haar H x ≠ 0)).card ≤ Nell d (ℓs t)) ∧
      (∀ ω, ∀ t : ℕ, ∀ H : HaarIdx d,
        haar H (lfPoint d ε ℓs Bs (X · ω) (Ξ · ω) (Y · ω) t) = 0 →
        disc (lfRun d ε ℓs Bs (X · ω) (Ξ · ω) (Y · ω) (t + 1)) H
          = disc (lfRun d ε ℓs Bs (X · ω) (Ξ · ω) (Y · ω) t) H) := by sorry

end QMCBeyondHK.Supplement
