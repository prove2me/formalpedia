-- Prove2me | Theorems.Thm_UpperTheory_V_Base_resU_conjRep
-- name    : UpperTheory.V.Base.resU_conjRep
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:13:10.454963+00:00
-- url     : https://prove2.me/theorems/c5993388-77ee-4224-b8c3-59075bb30c98
-- title:
--   Base: res U conj Rep
-- statement:
--   The Base construction uses the res U conj Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/RestrictionMemInvariantH1.lean#L184-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/RestrictionMemInvariantH1.lean#L184-L195

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

theorem UpperTheory.V.Base.resU_conjRep (ρ : Representation R G M) {U' U : Subgroup G} [U.Normal] [U'.Normal] (h : U' ≤ U) (g : G)
    (x : H1U ρ U) : resU ρ h (conjRep ρ U g x) = conjRep ρ U' g (resU ρ h x) := by sorry
