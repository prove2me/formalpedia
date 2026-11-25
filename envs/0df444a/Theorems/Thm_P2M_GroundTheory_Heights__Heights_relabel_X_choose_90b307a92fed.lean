-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_relabel_X_choose_90b307a92fed
-- name    : P2M_GroundTheory_Heights__Heights_relabel_X_choose_90b307a92fed
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:49:53.197898+00:00
-- url     : https://prove2.me/theorems/beafaa55-e5db-4411-9fa8-773861ec4415
-- title:
--   P2 M Ground Theory Heights  Heights relabel X choose 90b307a92fed: P2 M Ground Theory Heights  Heights relabel X choose 90b307a92fed
-- statement:
--   The P2 M Ground Theory Heights  Heights relabel X choose 90b307a92fed construction uses the P2 M Ground Theory Heights  Heights relabel X choose 90b307a92fed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L296-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Antisymmetric/PNefOnFibresRelabel.lean#L296-L301

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsNefRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
set_option linter.unusedSectionVars false
variable {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
  [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (ε : K ≃ K') (h : ∀ k, ι k = ι' (ε k))

theorem P2M_GroundTheory_Heights__Heights_relabel_X_choose_90b307a92fed (V : Ideal (MRing ι)) (hV : IsRelevant V)
    (hV' : IsRelevant (V.map (relabelRingEquiv ε h))) (k : K) :
    relabelRingEquiv ε h (X ⟨k, (hV k).choose⟩) = X ⟨ε k, (hV' (ε k)).choose⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«relabel_X_choose» := P2M_GroundTheory_Heights__Heights_relabel_X_choose_90b307a92fed
