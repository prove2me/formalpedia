-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_mapDomain_blockWeight_c47dcb6e8590
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_mapDomain_blockWeight_c47dcb6e8590
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:18:02.511149+00:00
-- url     : https://prove2.me/theorems/e540a340-e17a-418d-ac25-d5e1b3f5f9f3
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers weight map Domain block Weight c47dcb6e8590: P2 M Ground Theory Heights  Heights Field Numbers weight map Domain block Weight c47dcb6e8590
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers weight map Domain block Weight c47dcb6e8590 construction uses the P2 M Ground Theory Heights  Heights Field Numbers weight map Domain block Weight c47dcb6e8590 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameMultiHomog.lean#L28-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameMultiHomog.lean#L28-L51

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_mapDomain_blockWeight_c47dcb6e8590 {K K' : Type} [DecidableEq K] [DecidableEq K'] (j : K ↪ K')
    (ι : K → Type) (ι' : K' → Type) (g : (Σ k, ι k) → (Σ k', ι' k'))
    (hg : ∀ v, (g v).1 = j v.1) (u : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain g u) =
      Function.extend j (Finsupp.weight (blockWeight ι) u) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«weight_mapDomain_blockWeight» := P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_mapDomain_blockWeight_c47dcb6e8590
