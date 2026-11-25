-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_exists_delta_val
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.exists_delta_val
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:14:01.889926+00:00
-- url     : https://prove2.me/theorems/0fd63d70-9d43-5bca-80e4-d65d24e32787
-- title:
--   ERam: exists delta val
-- statement:
--   The ERam construction uses the exists delta val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamVal.lean#L289-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamVal.lean#L289-L310

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Formalism.L2.Pj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.exists_delta_val [IsGalois ℚ E] (ℓ a m : ℕ) (hℓ : ℓ.Prime) (hm : ¬ ℓ ∣ m)
    (hdisc : (discr E).natAbs = ℓ ^ a * m) (ψ : E →+* k) (hψ : Function.Injective ψ)
    (hℓψ : 0 < vV V (ψ (ℓ : E))) :
    ∃ δ : 𝓞 E, δ ∈ differentIdeal ℤ (𝓞 E) ∧ δ ≠ 0 ∧
      vV V (ψ (δ : E)) * Module.finrank ℚ E = a * vV V (ψ (ℓ : E)) := by sorry
