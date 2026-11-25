-- Prove2me | Theorems.Thm_UpperTheory_V_Base_selRep_of_mem
-- name    : UpperTheory.V.Base.selRep_of_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:40:59.181233+00:00
-- url     : https://prove2.me/theorems/db4e78fb-9e66-4a27-b826-a654e4b03c8b
-- title:
--   Base: sel Rep of mem
-- statement:
--   The Base construction uses the sel Rep of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/RestrictionMemInvariantH1.lean#L220-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/SelmerTransport/RestrictionMemInvariantH1.lean#L220-L223

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

theorem UpperTheory.V.Base.selRep_of_mem (ρ : Representation R G M) (U : Subgroup G) [U.Normal] {𝒟 : Set (Subgroup G)}
    (h𝒟 : ConjStable 𝒟) {g : G} (hg : g ∈ U) (x : LocSel ρ U 𝒟) : selRep ρ U h𝒟 g x = x := by sorry
