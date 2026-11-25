-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_smul_0aaa5ee7d0fc
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_smul_0aaa5ee7d0fc
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:20:32.978017+00:00
-- url     : https://prove2.me/theorems/2c162acf-e8d9-4dc3-b7fb-1caeef462777
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize smul 0aaa5ee7d0fc: P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize smul 0aaa5ee7d0fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize smul 0aaa5ee7d0fc construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top antisymmetrize smul 0aaa5ee7d0fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L58-L60

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_smul_0aaa5ee7d0fc (f N : ℕ) (b : ℚ) (H : RootRing f N) :
    antisymmetrize f N (b • H) = b • antisymmetrize f N H := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«antisymmetrize_smul» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_antisymmetrize_smul_0aaa5ee7d0fc
