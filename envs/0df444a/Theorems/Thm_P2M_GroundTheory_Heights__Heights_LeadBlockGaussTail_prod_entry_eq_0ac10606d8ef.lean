-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_prod_entry_eq_0ac10606d8ef
-- name    : P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_prod_entry_eq_0ac10606d8ef
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:03.568504+00:00
-- url     : https://prove2.me/theorems/cb31b803-9054-4bed-90dc-1dc4b73290a7
-- title:
--   P2 M Ground Theory Heights  Heights Lead Block Gauss Tail prod entry eq 0ac10606d8ef: P2 M Ground Theory Heights  Heights Lead Block Gauss Tail prod entry eq 0ac10606d8ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Lead Block Gauss Tail prod entry eq 0ac10606d8ef construction uses the P2 M Ground Theory Heights  Heights Lead Block Gauss Tail prod entry eq 0ac10606d8ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L252-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PLeadBlockGaussTail.lean#L252-L275

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PLeadBlockGaussTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LeadBlockGaussTail

theorem P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_prod_entry_eq_0ac10606d8ef {m k : ℕ} (hm : 0 < m) (K r : ℝ) (σ : Equiv.Perm (Fin m)) :
    ∏ i : Fin m, ∏ j : Fin (m + k), K / (1 + (if j = Fin.castAdd k ⟨0, hm⟩ then r else 0) ^ 2) ^
        ((if j = Fin.castAdd k (σ i) then 1 else 0) + 1) =
      K ^ (m * (m + k)) / (1 + r ^ 2) ^ (m + 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LeadBlockGaussTail».«prod_entry_eq» := P2M_GroundTheory_Heights__Heights_LeadBlockGaussTail_prod_entry_eq_0ac10606d8ef
