-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_uniformizer_of_residue_indep
-- name    : ReciprocityTheory.ChartRestriction.G.T0.uniformizer_of_residue_indep
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:37.99906+00:00
-- url     : https://prove2.me/theorems/1313af16-5b0f-5972-a46b-e6461a5ebcfd
-- title:
--   T0: uniformizer of residue indep
-- statement:
--   The T0 construction uses the uniformizer of residue indep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UniformizerOfResidueIndep.lean#L9-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/UniformizerOfResidueIndep.lean#L9-L59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValAlgebraMapEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial

theorem ReciprocityTheory.ChartRestriction.G.T0.uniformizer_of_residue_indep {Ω : Type} [Field Ω] {σ τ : Type}
    (w : AddValuation (FractionRing (MvPolynomial σ Ω)) (WithTop ℤ)) (hw : IsNormDiscrete w)
    (t : τ → FractionRing (MvPolynomial σ Ω)) (ht : ∀ s, t s ∈ vRing w)
    (hind : letI := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (vRing w) (algebraMap Ω (FractionRing (MvPolynomial σ Ω)))
      AlgebraicIndependent (IsLocalRing.ResidueField
          ((vRing w).comap (algebraMap Ω (FractionRing (MvPolynomial σ Ω)))))
        (fun s => IsLocalRing.residue (vRing w) ⟨t s, ht s⟩))
    (g : σ → MvPolynomial τ Ω)
    (hg : ∀ x, algebraMap (MvPolynomial σ Ω) (FractionRing (MvPolynomial σ Ω)) (X x) =
      aeval t (g x)) :
    ∃ π : Ω, w (algebraMap Ω (FractionRing (MvPolynomial σ Ω)) π) = 1 := by sorry
