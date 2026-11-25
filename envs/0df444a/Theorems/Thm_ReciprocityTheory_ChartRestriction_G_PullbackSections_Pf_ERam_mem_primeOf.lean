-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_mem_primeOf
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.mem_primeOf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:03:03.458869+00:00
-- url     : https://prove2.me/theorems/b504f9a1-a805-4ab1-84b6-ea66f0daa202
-- title:
--   ERam: mem prime Of
-- statement:
--   The ERam construction uses the mem prime Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamVal.lean#L106-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamVal.lean#L106-L107

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
variable (V)

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.mem_primeOf (ψ : E →+* k) (hψ : Function.Injective ψ) (x : 𝓞 E) :
    x ∈ primeOf (V := V) ψ hψ ↔ 0 < vV V (ψ (x : E)) ∨ x = 0 := by sorry
