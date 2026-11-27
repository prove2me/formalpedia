-- Prove2me | Theorems.Thm_UpperTheory_V_Base_selRes_selRep
-- name    : UpperTheory.V.Base.selRes_selRep
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:40:41.691882+00:00
-- url     : https://prove2.me/theorems/08b91ce7-8210-5b8a-b7c7-1012001ab965
-- title:
--   Base: sel Res sel Rep
-- statement:
--   The Base construction uses the sel Res sel Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/RestrictionMemInvariantH1.lean#L225-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/RestrictionMemInvariantH1.lean#L225-L230

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_SelmerTransport_RestrictionMemInvariantH1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.Gal
open UpperTheory UpperTheory.V UpperTheory.V.Base
variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
variable [IsTopologicalGroup G] [DiscreteTopology M]

theorem UpperTheory.V.Base.selRes_selRep (ρ : Representation R G M) {U' U : Subgroup G} [U.Normal] [U'.Normal] (h : U' ≤ U)
    {𝒟 : Set (Subgroup G)} (h𝒟 : ConjStable 𝒟) (g : G) (x : LocSel ρ U 𝒟) :
    selRes ρ h 𝒟 (selRep ρ U h𝒟 g x) = selRep ρ U' h𝒟 g (selRes ρ h 𝒟 x) := by sorry
