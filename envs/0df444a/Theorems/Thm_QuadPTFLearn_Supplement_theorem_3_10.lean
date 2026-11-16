-- Prove2me | Theorems.Thm_QuadPTFLearn_Supplement_theorem_3_10
-- name    : QuadPTFLearn.Supplement.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:41:59.17329+00:00
-- url     : https://prove2.me/theorems/2a0293da-45d5-45c5-83fa-68f9ae4cc140
-- title:
--   Theorem 3.10, p.25 — learning a regular instance (each quadratic $(\tau,\{0\})$-regular) to error $\varepsilon$ w.p. 2/3 with $d^{O(1)}(k/\varepsilon)^{O(k^2)}$ samples and time
-- statement:
--   **Efficiently learning a regular instance.** There is an algorithm with the following guarantee. Let $d,k\ge1$ be integers and $\varepsilon\in(0,1/2)$, and let $D$ be a distribution over $\mathbb R^d\times\{0,1\}$ with marginal $D_x=N(0,I_d)$. Suppose some intersection
--   $$f(x)=1\{p_1(x)\ge0,\dots,p_k(x)\ge0\}$$
--   of polynomials $p_i$ of degree at most two satisfies:
--
--   1. each $p_i$ is individually $(\tau,\{0\})$-regular for some $\tau\in(0,1)$ with $\tau\le(\varepsilon/k)^c$, i.e. $\mathbb E_{x\sim N(0,I_d)}[(v\cdot\nabla p_i(x))^2]\le\tau^2\,\mathrm{Var}[p_i]$ for every unit vector $v$;
--   2. $\Pr_{(x,y)\sim D}[f(x)\ne y]\le(\varepsilon/k)^c$,
--
--   where $c$ is a universal constant. Given $k$, $\varepsilon$ and i.i.d. samples from $D$, the algorithm uses at most
--   $$C\,d^{C}\,(k/\varepsilon)^{Ck^2}$$
--   samples and arithmetic operations, for a universal constant $C$. With probability at least $2/3$ it outputs an intersection of quadratic threshold functions $h:\mathbb R^d\to\{0,1\}$ with
--   $$\Pr_{(x,y)\sim D}[h(x)\ne y]\le\varepsilon .$$
--
--   This is the fully regular case $V=\{0\}$ of the paper's subspace framework, in which no defining quadratic has a large share of its variance along any single direction; it is the base case that the general learner reduces to after dimension reduction.
--
--   **Formalization Note** One program `P` and the constants $c$, $C$ are chosen before $d$, $k$, $\varepsilon$ and $D$. The machine is `QuadPTFLearn.Machine`. The output is read with `decodeInter`.
--
--   Differences from the source:
--   - reading: "there is an algorithm … uses/draws … samples, runs in … time", model unspecified → one admissible program of the deterministic arithmetic sampling real RAM (exact + − × ÷, comparisons, pointers; no √, exp, log, floor, coin; unit cost, `sample` costs d+1), chosen before every parameter and the distribution, with samples and work bounded on every sample stream; reason: the paper fixes no model and its proofs count arithmetic operations; a single uniform program with worst-case bounds is the non-weaker reading (the convention of the published theorem_1_3)
--   - encoding: d^{O(1)}(k/ϵ)^{O(k²)} time and sample complexity → samples ≤ C·d^C·(k/ε)^{C·k²} and work ≤ the same, one C : ℕ chosen with the program; reason: the meaning of O(1) and O(k²) for d ≥ 1 and k/ε > 2; one constant for both bounds is equivalent to two
--   - encoding: τ ≤ (ϵ/k)^c and Pr_D[f(x) ≠ y] ≤ (ϵ/k)^c, c a sufficiently large universal constant → ∃ c : ℕ chosen with the program, before d, k, ε, D; both hypotheses use the same (ε/k)^c; reason: since ε/k < 1, a larger c only strengthens the hypotheses, so 'for c sufficiently large' is 'for some c', and an integer c is no loss
--   - encoding: each p_i is individually (τ, {0})-regular (Definition 3.1, τ ∈ (0,1)) → ∃ τ with 0 < τ < 1 and τ ≤ (ε/k)^c such that IsRegular τ ⊥ (p i) for every i; reason: V = {0} is the zero submodule, whose orthogonal complement is ℝᵈ; Definition 3.1's standing τ ∈ (0, 1)
--   - generalization: outputs a hypothesis h : ℝᵈ → {0, 1} → output memory that decodes (decodeInter) to an intersection 1{q_j(x) ≥ 0 for all j < m} of quadratics; an undecodable output is a failure; reason: Algorithm 1 returns ĥ in exactly this family H (steps 7–9); every decoded intersection is a {0,1}-valued hypothesis, so the statement specializes to Theorem 3.10
--   - encoding: D a distribution over ℝᵈ × {0, 1} with marginal D_x = N(0, I_d); error Pr_{(x,y)∼D}[h(x) ≠ y] → a probability law on ℝᵈ × ℝ with marginal N(0, I_d) and labels in {0,1} almost surely (IsBoolGaussLaw); error D{(x, y) : h(x) ≠ y}; the stream is i.i.d. from D; reason: the same laws and the same error
--   - encoding: given k, ϵ and i.i.d. sample access to D; with probability at least 2/3 → input list [k, ε] in memory from cell 0, d + 1 in pointer register 0; a measurable set of sample streams of probability ≥ 2/3 on which every halted state decodes to a hypothesis of error ≤ ε; reason: input convention of the machine; the same event
-- source:
--   Diakonikolas, Kane, Ma, Ren, Tran, Beyond Multi-Index Models: Learning Intersections of Degree-2 PTFs, arXiv:2611.05114 (sha256 4d6ea892…), Theorem 3.10 (Efficiently Learning a Regular Instance), p.25 (PDF p.27); Definition 3.1, p.15 (PDF p.17); Algorithm 1, p.26 (PDF p.28)

import Mathlib
import Definitions.Def_QuadPTFLearn_Learner
import Definitions.Def_QuadPTFLearn_Regularity
import Definitions.Def_QuadPTFLearn_Influence
import Definitions.Def_QuadPTFLearn_Supplement_InterHyp

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuadPTFLearn

namespace Supplement

/-- I. Diakonikolas, D. M. Kane, M. Ma, L. Ren, T. Tran, *Beyond Multi-Index Models: Learning
Intersections of Degree-2 PTFs*, arXiv:2611.05114 (held copy, sha256 4d6ea892…5aed).
Theorem 3.10 (Efficiently Learning a Regular Instance), p.25 (PDF p.27), with Definition 3.1,
p.15 (PDF p.17), and Algorithm 1, p.26 (PDF p.28).

There is one admissible program `P`, a universal constant `c` and a constant `C` such that for all
integers `d, k ≥ 1`, every `ε ∈ (0, 1/2)` and every distribution `D` on `ℝᵈ × {0, 1}` with marginal
`N(0, I_d)`: if some intersection `f = 1{p₁ ≥ 0, …, p_k ≥ 0}` of polynomials of degree at most two,
each individually `(τ, {0})`-regular with `τ ≤ (ε/k)^c`, has `Pr_D[f(x) ≠ y] ≤ (ε/k)^c`, then the
program, run on input `[k, ε]` and i.i.d. examples of `D`,
1. halts on every stream after at most `C d^C (k/ε)^{C k²}` samples and work;
2. with probability at least `2/3` outputs an intersection of quadratic PTFs `h` with
   `Pr_{(x,y)∼D}[h(x) ≠ y] ≤ ε`.

**Formalization Note.** `P`, `c` and `C` are chosen before `d, k, ε, D` (one algorithm; `c` is
the single "sufficiently large universal constant", and a larger `c` only strengthens the
hypotheses). `(τ, {0})`-regularity is `IsRegular τ ⊥ (p i)` for each `i`, with Definition 3.1's
`τ ∈ (0, 1)`. The machine is `QuadPTFLearn.Machine` (no square root, floor or coin; `sample`
costs `d + 1`); the dimension is read from pointer register `0`. The output layout is
`decodeInter`; an undecodable output is a failure. -/
theorem theorem_3_10 :
    ∃ P : Program, Admissible P ∧ ∃ c C : ℕ,
      ∀ k d : ℕ, 1 ≤ k → 1 ≤ d → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∀ (D : Measure (Pt d × ℝ)) [IsProbabilityMeasure D], IsBoolGaussLaw D →
      ∀ p : Fin k → Poly d, IsQuadFamily p →
        (∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧ τ ≤ (ε / k) ^ c ∧ ∀ i, IsRegular τ ⊥ (p i)) →
        D {z | ptfInd p z.1 ≠ z.2} ≤ ENNReal.ofReal ((ε / k) ^ c) →
        HaltsWithin P (d + 1) (initState (d + 1) [(k : ℝ), ε])
            (C * (d : ℝ) ^ C * ((k : ℝ) / ε) ^ (C * k ^ 2))
            (C * (d : ℝ) ^ C * ((k : ℝ) / ε) ^ (C * k ^ 2)) ∧
        SucceedsWP P (d + 1) (initState (d + 1) [(k : ℝ), ε])
          (Measure.infinitePi (fun _ : ℕ => jointLaw D)) (2 / 3)
          (fun s => ∃ H : InterHyp d, decodeInter d (outMem s) (outBase s) = some H ∧
            D {z | H.eval z.1 ≠ z.2} ≤ ENNReal.ofReal ε) := by sorry

end Supplement

end QuadPTFLearn
