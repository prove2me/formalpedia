-- Prove2me | Theorems.Thm_SmoothBerr_Supplement_theorem_2_3
-- name    : SmoothBerr.Supplement.theorem_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:56:48.611534+00:00
-- url     : https://prove2.me/theorems/43cbb04a-29db-423b-bbb1-516cc248e513
-- title:
--   Theorem 2.3 — symmetric systems: $O(1/\varepsilon)$ deterministic matvecs suffice, $(e^{-1}-o(1))/\varepsilon$ needed (corrected: consistent $Ax=b$, $\lceil5/\varepsilon\rceil+1$ matvecs)
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ be symmetric.
--
--   1. **Upper bound.** For every $\varepsilon>0$ and every $n$ there is a deterministic adaptive algorithm that only computes matvecs $x\mapsto Ax$ and, for every symmetric $A$ and every $b$ in the range of $A$ (the system $Ax=b$ is consistent), halts after at most $\lceil5/\varepsilon\rceil+1$ matvecs and returns $\tilde x$ with $\mathrm{berr}(A,b,\tilde x)\le\varepsilon$.
--   2. **Optimality.** For every $\delta>0$ there is $\varepsilon_0>0$ such that for all $0<\varepsilon<\varepsilon_0$ and all $t$: if for every $n$ there is a randomized adaptive algorithm with $t$ matvecs that, for every symmetric invertible $A\in\mathbb R^{n\times n}$ and every $b$, returns $\tilde x$ with $\mathrm{berr}(A,b,\tilde x)\le\varepsilon$ with probability at least $2/3$, then
--   $$
--   t\ \ge\ \frac{e^{-1}-\delta}{\varepsilon}.
--   $$
--
--   For symmetric systems the condition-number dependence that Theorem 4.3 forces on general systems disappears: backward error $\varepsilon$ costs $\Theta(1/\varepsilon)$ matvecs, deterministically, and randomization cannot improve the leading constant beyond $e^{-1}$.
--
--   **Formalization Note** The upper half counts matvecs with $A$ only. In the lower half the probability is over the algorithm's seed; the algorithm may depend on $n$, and success is required only on invertible matrices.
--
--   Differences from the source:
--   - correction: t ≤ 5/ε deterministic matvecs → halts within ⌈5/ε⌉₊ + 1 matvecs; reason: for ε > 5 the printed bound allows 0 matvecs, and an output depending on b alone fails on A = δI, b ≠ 0, as δ → 0 (‖δx̃ − b‖₂ → ‖b‖₂ > 0 while εδ‖x̃‖₂ → 0); the paper's proof (a degree-⌈5/ε⌉ polynomial from Theorem 4.7, then minimizing the backward error over K_k(A, b), whose residuals need A^{k+1}b) certifies ⌈5/ε⌉ + 1 matvecs
--   - correction: every symmetric A and every b → every symmetric A and every b in the range of A (∃ x₀, A x₀ = b) in the upper half; reason: if b ≠ 0 lies in the kernel of A and n ≥ t + 2, let v₁, …, v_t be the queries the deterministic algorithm makes when every answer is 0, take a unit e ⊥ b, v₁, …, v_t and A_δ = δeeᵀ (symmetric, nonzero): every answer is 0 for every δ > 0, so the output x̃ is fixed, and berr(A_δ, b, x̃) ≤ ε forces ‖b‖₂ ≤ (1 + ε)δ‖x̃‖₂ → 0, a contradiction (A = 0, b ≠ 0 fails the same way); for b in the range of A the weights of Eq. (6) sit on nonzero eigenvalues and the proof via Theorem 4.7 applies
--   - reading: the lower half prints no success probability → success with probability ≥ 2/3; reason: the lower half is proved as Theorem 9.2 (p.4: 'Section 9 (lower bound)'), which assumes probability ≥ 2/3; requiring probability 1 would be the weaker theorem
--   - reading: t ≥ (e⁻¹ − o(1))/ε → ∀ δ > 0, ∃ ε₀ > 0, ∀ ε ∈ (0, ε₀), the bound (e⁻¹ − δ)/ε ≤ t; reason: Theorem 9.2: 'the little-oh shrinks as ε grows small'
--   - generalization: an algorithm that solves any symmetric linear system → for every n some algorithm (allowed to depend on n) succeeds on every symmetric invertible A ∈ ℝ^{n×n} and every b; reason: the hypothesis is weaker than one algorithm for all n and all symmetric systems, so the theorem is stronger; for fixed n, n matvecs solve exactly, so the statement concerns all dimensions
--   - reading: a (potentially randomized) algorithm → a seed ω from a probability law μ on a measurable space; queries and output measurable jointly in the seed and the answers; reason: the measurability that a success probability presupposes
--   - encoding: matvecs with a symmetric A → queries v ↦ Av only (OnlyMulA, RandMatvecAlg); reason: Aᵀv = Av for symmetric A
-- source:
--   Dereziński, Mahoney, Meyer, Musco, From smoothed analysis to backward error: The power of adaptive perturbations (manuscript of 3 Nov 2026, STOC 2027 submission; sha256 9575cd20bc2c854eb092a4950988f7fbef8715adda344a1ba39489bc28b4e58d), Theorem 2.3, p.4 (proved in §8 and in Theorem 9.2, p.24)

import Mathlib
import Definitions.Def_SmoothBerr_Supplement_BerrLe
import Definitions.Def_SmoothBerr_Supplement_DetMatvecAlg
import Definitions.Def_SmoothBerr_Supplement_RandMatvecAlg

open MeasureTheory Matrix
open scoped ENNReal

namespace SmoothBerr.Supplement

/-- **Theorem 2.3 (Solving symmetric systems to backward error deterministically)** (Dereziński, Mahoney, Meyer, Musco, *From smoothed analysis to backward error: The power of adaptive perturbations*, manuscript of 3 Nov 2026, sha256 9575cd20…, Theorem 2.3, p.4; proved in §8 and §9, Theorem 9.2, p.24) (corrected: consistent systems `b ∈ range A`, `⌈5/ε⌉ + 1` matvecs).

Let `A ∈ ℝ^{n×n}` be symmetric. The system `Ax = b` can be solved to backward error `ε` using
deterministic matvecs with `A`. Moreover this is optimal: any (potentially randomized) algorithm
requires `t ≥ (e⁻¹ − o(1))/ε` matvecs to solve a symmetric linear system to backward error `ε`.

**Formalization Note**
1. Upper half: for every `ε > 0` and `n` there is a deterministic algorithm querying only
   `x ↦ A x` that halts within `⌈5/ε⌉ + 1` matvecs on every symmetric `A` and every `b` in the
   range of `A` (the system `Ax = b` is consistent) with backward error `≤ ε`. The page prints
   `t ≤ 5/ε` for every symmetric `A` and every `b`. Both are corrected: if `b ≠ 0` lies in the
   kernel of `A ≠ 0` and `n ≥ t + 2`, take a unit `e` orthogonal to `b` and to the `t` queries the
   algorithm makes when every answer is `0`, and `A_δ = δ e eᵀ`; every answer is `0` for every
   `δ > 0`, so the output `x̃` is fixed, while `berr ≤ ε` forces `‖b‖₂ ≤ (1 + ε) δ ‖x̃‖₂ → 0`
   (the case `A = 0`, `b ≠ 0` fails the same way); for `ε > 5` the printed bound allows
   `0` matvecs, and an output depending on `b` alone fails on `A = δI` as `δ → 0`. The paper's
   proof (degree `⌈5/ε⌉` polynomial of Theorem 4.7, then the minimal backward error over the
   Krylov subspace, whose residuals need `A^{k+1}b`) uses `⌈5/ε⌉ + 1` matvecs.
2. Lower half: `o(1)` is a limit as `ε → 0`: for every `δ > 0` there is `ε₀ > 0` such that for
   `ε < ε₀`, if for every `n` some randomized algorithm with `t` matvecs (`RandMatvecAlg`, seed
   law `μ`) returns, for every symmetric invertible `A` and every `b`, a vector with backward
   error `≤ ε` with probability `≥ 2/3`, then `(e⁻¹ − δ)/ε ≤ t`. The success probability `2/3`
   is that of Theorem 9.2, the formal version of this half. Success is required only on invertible
   `A`. -/
theorem theorem_2_3 :
    (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∃ Φ : DetMatvecAlg n, Φ.OnlyMulA ∧
      ∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsSymm → ∀ b : Fin n → ℝ,
        (∃ x₀ : Fin n → ℝ, A *ᵥ x₀ = b) →
        Φ.HaltsWithin A b (⌈5 / ε⌉₊ + 1) ∧
          BerrLe A b (Φ.outputAt A b (⌈5 / ε⌉₊ + 1)) ε) ∧
    (∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ t : ℕ,
      (∀ n : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ ∧ ∃ alg : RandMatvecAlg n t Ω,
          ∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsSymm → IsUnit A.det → ∀ b : Fin n → ℝ,
            (2 / 3 : ℝ≥0∞) ≤ μ {ω | BerrLe A b (alg.run A b ω) ε}) →
      (Real.exp (-1) - δ) / ε ≤ t) := by sorry

end SmoothBerr.Supplement
