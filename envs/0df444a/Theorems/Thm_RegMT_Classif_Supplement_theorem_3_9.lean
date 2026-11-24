-- Prove2me | Theorems.Thm_RegMT_Classif_Supplement_theorem_3_9
-- name    : RegMT.Classif.Supplement.theorem_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:30:51.173985+00:00
-- url     : https://prove2.me/theorems/342a4786-9f64-4afd-b0a0-bf57878ea5b8
-- title:
--   Theorem 3.9 — robust regression comparison
-- statement:
--   Let $L$ be convex, nonnegative and Lipschitz continuous on $\mathbb R$. Use the full input-output space with an arbitrary joint norm, $N\ge1$ training samples, and $\rho\ge0$. For every linear hypothesis $w$,
--   $$\sup_{\frac1N\sum_i\|\Delta\xi_i\|\le\rho}\frac1N\sum_iL(r_w(\hat\xi_i+\Delta\xi_i))\le\sup_{Q\in B_\rho(\hat P_N)}\mathbb E_Q L(r_w(\xi)).$$
--   Under Assumption 3.7 the two values are equal. That assumption requires, for every weight, a sample where the loss derivative exists and has magnitude equal to its exact Lipschitz modulus. It is imposed only in the equality clause. This compares distributional and samplewise robustness for every convex Lipschitz loss, including losses that are not piecewise affine.
--
--   Differences from the source:
--   - encoding: Finite Euclidean coordinates, ordinary expectations and mathematical optimization notation. → Coordinate-free normed spaces or real Hilbert spaces, extended nonnegative integrals and guarded extended extrema, with all sample and piece ranges explicit.; reason: These representations preserve the source domain, arbitrary norms, exact constants, and infinite values; nonnegative loss and measurable probability spaces are the standing conventions.
-- source:
--   Shafieezadeh-Abadeh, Kuhn & Mohajerin Esfahani, Regularization via Mass Transportation, arXiv:1710.10016v3, p. 11, Theorem 3.9; Appendix A proof

import Mathlib
import Definitions.Def_RegMT_Classif_Supplement_Perturbation

open scoped ENNReal

namespace RegMT.Classif.Supplement

theorem theorem_3_9 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {n N : ℕ}
    (e : E ≃L[ℝ] (Fin n → ℝ) × ℝ) (hN : 0 < N) (z : Fin N → E)
    (L : ℝ → ℝ) (hconvex : ConvexOn ℝ Set.univ L) (hnonneg : ∀ t, 0 ≤ L t)
    (hlip : ∃ K, LipschitzWith K L) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∀ w : Fin n → ℝ,
      robustReg z L (RegMT.Regress.pairing e w) ρ ≤
        normRisk Set.univ z ρ (fun ξ => L (RegMT.Regress.pairing e w ξ)) ∧
      (MinimalDispersion e z L →
        normRisk Set.univ z ρ (fun ξ => L (RegMT.Regress.pairing e w ξ)) =
          robustReg z L (RegMT.Regress.pairing e w) ρ) := by sorry

end RegMT.Classif.Supplement
