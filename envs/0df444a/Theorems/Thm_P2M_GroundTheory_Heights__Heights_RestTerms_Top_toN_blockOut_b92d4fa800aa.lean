-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_toN_blockOut_b92d4fa800aa
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_toN_blockOut_b92d4fa800aa
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:33.349802+00:00
-- url     : https://prove2.me/theorems/24fed657-2ead-4c56-80a2-505299d347a3
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top to N block Out b92d4fa800aa: P2 M Ground Theory Heights  Heights Rest Terms Top to N block Out b92d4fa800aa
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top to N block Out b92d4fa800aa construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top to N block Out b92d4fa800aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L131-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L131-L175

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_toN_blockOut_b92d4fa800aa (r a : ℕ) (c : SmallBlock) (κ : ℚ) (q m k : ℕ) (hk : q + m = k + r * a) :
    toN (r + a) (blockOut r a c κ q m) =
      C κ * ∑ nu ∈ partitionsOf r k, C (blockCoeff q m (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«toN_blockOut» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_toN_blockOut_b92d4fa800aa
