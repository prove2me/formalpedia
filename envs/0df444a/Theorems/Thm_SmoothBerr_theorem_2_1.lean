-- Prove2me | Theorems.Thm_SmoothBerr_theorem_2_1
-- name    : SmoothBerr.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:27.937282+00:00
-- url     : https://prove2.me/theorems/dd29757c-0f4a-4575-9435-456f63094b6c
-- title:
--   Theorem 2.1 — smoothed analysis does not help: $t\gtrsim n$ matvecs for any oblivious perturbation
-- statement:
--   There are universal constants $c,p\in(0,1)$ and $C>0$ such that the following holds for every $n$. Fix any distribution of a random matrix $\Delta\in\mathbb R^{n\times n}$ with $\|\Delta\|_2\le c$. Consider an algorithm that takes a vector $b$, computes $t$ matvecs with $\hat A=A+\Delta$ (and possibly with $\hat A^\top$), and returns a vector $\tilde x$. If for every matrix $A\in\mathbb R^{n\times n}$ with $\|A\|_2\le1$ and every $b\ne0$
--   $$
--   \|\tilde x-\hat A^{-1}b\|_2\le\frac1{20}\|\hat A^{-1}b\|_2\qquad\text{with probability at least }p,
--   $$
--   then $t\ge Cn$.
--
--   Perturbing the input by a random matrix chosen before the input is seen, and then solving to small forward error, is the standard smoothed-analysis route to a small backward error. The theorem shows that this route costs $\Omega(n)$ matvecs, while an adaptive perturbation achieves backward error $\varepsilon$ with $O(\log(n)/\varepsilon)$ matvecs.
--
--   **Formalization Note**
--   1. The constants $c,p,C$ are chosen before $n$, the law of $\Delta$, $t$ and the algorithm; every probability law of $\Delta$ with $\|\Delta\|_2\le c$ almost surely is allowed, including point masses.
--   2. The algorithm is a randomized adaptive paired matvec algorithm with $t$ steps whose seed is independent of $\Delta$; the probability is over the seed and $\Delta$ for fixed $A$ and $b$.
--   3. A singular $\hat A$ counts as a success.
--
--   Differences from the source:
--   - generalization: an algorithm that computes at most t matvecs with Â → a randomized adaptive paired matvec algorithm with exactly t steps, each returning both Âᵀu and Âv; reason: each matvec with Â (or Âᵀ) is part of one paired step, and an algorithm with fewer steps ignores its last answers; a lower bound against the larger class specializes to the printed one
--   - generalization: success ‖x̃ − Â⁻¹b‖₂ ≤ (1/20)‖Â⁻¹b‖₂ required for every b → success required only for b ≠ 0, and a singular Â counts as a success (Solves); reason: the hypothesis is weaker, so the theorem is stronger; it specializes to the printed statement
--   - reading: a randomized algorithm succeeding "with probability" → a seed ω drawn from a probability law μ on a measurable space Ω, independent of the matrices; queries and output measurable jointly in the seed and the answers; reason: the measurability that a probability of success presupposes; the seed is the algorithm's own randomness
--   - generalization: an algorithm that takes b (measurable in b, implicitly) → no measurability in the input b: query and output may depend on b arbitrarily (PairedMatvecAlg requires measurability only in the seed and the answers, for each fixed b); reason: the hypothesis is a per-b guarantee, so the Lean class contains every measurable algorithm and the bound specializes to the printed one; the proof averages over random right-hand sides, which can be taken from the finite Rademacher set {±1}ⁿ (Hutchinson bounds E[Y] = ‖Â⁻¹‖_F², E[Y²] ≤ 3‖Â⁻¹‖_F⁴ hold for it too), where measurability in b is automatic
--   - encoding: fix any distribution over random matrices Δ with ‖Δ‖₂ ≤ c → any probability measure ν on n × n matrices with ‖Δ‖₂ ≤ c ν-a.s.; reason: same distributions
--   - encoding: universal constants c, p ∈ (0,1); t ≳ n in the worst case → ∃ c, p ∈ (0,1), ∃ C > 0, before n, ν, t and the algorithm, with C·n ≤ t; the hypothesis quantifies over every A with ‖A‖₂ ≤ 1; reason: §3, p.4: ≳ hides a universal constant; the worst case is over A and b
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 2.1, p.3

import Mathlib
import Definitions.Def_GaussianMatrix_basic
import Definitions.Def_SmoothBerr_PairedMatvecAlg
import Definitions.Def_SmoothBerr_Solves

open MeasureTheory ProbabilityTheory Matrix GaussianMatrix

namespace SmoothBerr

/-- **Theorem 2.1 (Smoothed analysis does not help)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 2.1, p.3).

There are universal constants `c, p ∈ (0,1)` such that the following holds. Fix any distribution
over random matrices `Δ ∈ ℝ^{n×n}` with `‖Δ‖₂ ≤ c`. For any `A ∈ ℝ^{n×n}` with `‖A‖₂ ≤ 1` write
`Â = A + Δ`. Any algorithm that takes a vector `b`, computes at most `t` matvecs with `Â`, and
returns `x̃` with `‖x̃ − Â⁻¹b‖₂ ≤ (1/20)‖Â⁻¹b‖₂` with probability at least `p` must use `t ≳ n`
matvecs in the worst case.

**Formalization Note**
1. Quantifiers: `c, p ∈ (0,1)` and `C > 0` (the constant of `≳`, §3 p.4) are chosen first; then
   for every `n`, every probability law `ν` of `Δ` with `‖Δ‖₂ ≤ c` `ν`-a.s. (Dirac laws included),
   every `t` and every algorithm, the success hypothesis implies `C n ≤ t`.
2. Algorithms are randomized adaptive *paired* matvec algorithms with exactly `t` steps
   (`PairedMatvecAlg`): each step returns both `Âᵀu` and `Âv`, so any algorithm with at most `t`
   matvecs with `Â` is one of them. The seed has a law `μ` independent of `Δ`; queries and output
   are measurable in the seed and the answers.
3. The hypothesis asks success probability at least `p` over `μ ⊗ ν` for every `A` with
   `‖A‖₂ ≤ 1` (`specNorm`) and every `b ≠ 0`; success is `Solves`, which also counts a singular
   `Â` as a success. Both relaxations make the hypothesis weaker and the theorem stronger. -/
theorem theorem_2_1 :
    ∃ c p C : ℝ, 0 < c ∧ c < 1 ∧ 0 < p ∧ p < 1 ∧ 0 < C ∧
      ∀ (n t : ℕ) (ν : Measure (Fin n → Fin n → ℝ)) [IsProbabilityMeasure ν],
        (∀ᵐ Δ ∂ν, specNorm (Matrix.of Δ) ≤ c) →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (alg : PairedMatvecAlg n t (Fin n → ℝ) Ω (Fin n → ℝ)),
          (∀ A : Matrix (Fin n) (Fin n) ℝ, specNorm A ≤ 1 → ∀ b : Fin n → ℝ, b ≠ 0 →
            ENNReal.ofReal p ≤ (μ.prod ν)
              {q | Solves (A + Matrix.of q.2) b (alg.run (A + Matrix.of q.2) b q.1)}) →
          C * n ≤ t := by sorry

end SmoothBerr
