-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P15_relativeDistance_leadingSharpness
-- name    : QAlgorithms.Papers.Independent.Dependency50.P15.relativeDistance_leadingSharpness
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:25:45.483123+00:00
-- url     : https://prove2.me/theorems/41798890-eec5-46cb-8790-aa0fbf97128a
-- title:
--   Unnumbered after Corollary 8: sharp leading dimension coefficient
-- statement:
--   For every integer $d\ge2$, take $C=\mathrm{SEP}(\mathbb C^d:\mathbb C^d)$, $\rho=\Phi_d$ the maximally entangled density, and $\sigma=|00\rangle\langle00|$. These are density states with $T(\rho,\sigma)\le1$, and
--
--   $$D_C(\rho)-D_C(\sigma)=\kappa=\log_2d,\qquad E_R^\infty(\rho)-E_R^\infty(\sigma)=\log_2d.$$
--
--   Here $\kappa$ is the actual variation of $D_C$, $E_R=D_C$, and $E_R^\infty$ is its regularization. For every real $c<1$, every real additive offset $K$, and every dimension threshold, some dimension above that threshold has both differences strictly larger than $c\log_2d+K$.
--
--   Thus the universal leading coefficient cannot be reduced while keeping a dimension-independent additive offset. This does not assert equality in the complete finite-dimension continuity formula.
-- source:
--   Tight uniform continuity bounds for quantum entropies: conditional entropy, relative entropy distance and energy constraints, arXiv:1507.07775v6, PDF p. 6, Unnumbered after Corollary 8: sharp leading dimension coefficient

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P15

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P15

open QAlgorithms.Papers.Independent.Information100.P08 (bellVector)

/-- Unnumbered sharpness after Corollary 8, PDF p.6. Dimensions d=k+2 cover exactly
d≥2. The maximally entangled/pure-product family realizes kappa=log₂d for SEP;
both the single-letter and regularized differences preclude a smaller universal
leading coefficient with any fixed additive offset. No T=1 equality is asserted. -/
theorem relativeDistance_leadingSharpness :
    (∀ k : ℕ,
      let d := k + 2
      let phi := (pureDensity (bellVector d))
      let sigma := zeroProductDensity d
      IsDensityMatrix phi ∧ IsDensityMatrix sigma ∧ traceDistance phi sigma ≤ 1 ∧
      relativeEntanglementValue phi - relativeEntanglementValue sigma = Real.logb 2 (d : ℝ) ∧
      relativeVariation {gamma : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ |
        Entanglement.IsSeparableDensity gamma} = Real.logb 2 (d : ℝ) ∧
      regularizedRelativeEntanglement phi - regularizedRelativeEntanglement sigma =
        Real.logb 2 (d : ℝ)) ∧
    (∀ c K : ℝ, c < 1 → ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧
      let d := k + 2
      c * Real.logb 2 (d : ℝ) + K <
        relativeEntanglementValue (pureDensity (bellVector d)) - relativeEntanglementValue (zeroProductDensity d) ∧
      c * Real.logb 2 (d : ℝ) + K <
        regularizedRelativeEntanglement (pureDensity (bellVector d)) -
          regularizedRelativeEntanglement (zeroProductDensity d)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P15

end
