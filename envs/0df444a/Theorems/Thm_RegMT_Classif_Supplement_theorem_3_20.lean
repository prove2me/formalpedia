-- Prove2me | Theorems.Thm_RegMT_Classif_Supplement_theorem_3_20
-- name    : RegMT.Classif.Supplement.theorem_3_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:32:29.501942+00:00
-- url     : https://prove2.me/theorems/2c91d126-0811-45de-b931-e6bfe73f2295
-- title:
--   Theorem 3.20 — label-preserving robust comparison
-- statement:
--   Let $L$ be convex, nonnegative and Lipschitz continuous. Use the full finite-dimensional feature space with any norm, $N\ge1$ samples, $\rho\ge0$, and infinite label-switching cost. For every $w$,
--   $$\sup_{\frac1N\sum_i\|\Delta x_i\|\le\rho}\frac1N\sum_iL(\hat y_i\langle w,\hat x_i+\Delta x_i\rangle)\le\sup_{Q\in B_\rho(\hat P_N)}\mathbb E_Q L(y\langle w,x\rangle).$$
--   Under Assumption 3.18 the two values are equal. That condition quantifies over every weight and requires a sample at which the derivative at the signed margin exists and attains the magnitude of the exact Lipschitz modulus. It appears only in the equality clause. Infinite price is implemented by an infinite cost for every mismatched-label pair, rather than by a finite approximation.
--
--   Differences from the source:
--   - encoding: Finite Euclidean coordinates, ordinary expectations and mathematical optimization notation. → Coordinate-free normed spaces or real Hilbert spaces, extended nonnegative integrals and guarded extended extrema, with all sample and piece ranges explicit.; reason: These representations preserve the source domain, arbitrary norms, exact constants, and infinite values; nonnegative loss and measurable probability spaces are the standing conventions.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 14, Theorem 3.20; Appendix A proof

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Perturbation

open scoped ENNReal

namespace RegMT.Classif.Supplement

theorem theorem_3_20 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {N : ℕ}
    (hN : 0 < N) (x : Fin N → V) (y : Fin N → Bool) (L : ℝ → ℝ)
    (hconvex : ConvexOn ℝ Set.univ L) (hnonneg : ∀ t, 0 ≤ L t)
    (hlip : ∃ K, LipschitzWith K L) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ w : V →L[ℝ] ℝ,
      robustClass x y L w ρ ≤ costRisk labelPreservingCost Set.univ (fun i => (x i, y i)) ρ
        (fun ξ => L (DRLogReg.Reformulation.sgn ξ.2 * w ξ.1)) ∧
      (Nonseparability x y L →
        costRisk labelPreservingCost Set.univ (fun i => (x i, y i)) ρ
          (fun ξ => L (DRLogReg.Reformulation.sgn ξ.2 * w ξ.1)) =
            robustClass x y L w ρ) := by sorry

end RegMT.Classif.Supplement
