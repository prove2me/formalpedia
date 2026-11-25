-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__div_rpow_le_inv_pow_11dc30a365ee
-- name    : P2M_Formalism_MainNotions_BridgeLemma__div_rpow_le_inv_pow_11dc30a365ee
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:59:15.148642+00:00
-- url     : https://prove2.me/theorems/f1d1cc20-1ea6-4f53-8cf0-6ade2ddbdd6f
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  div rpow le inv pow 11dc30a365ee: P2 M Formalism Main Notions Bridge Lemma  div rpow le inv pow 11dc30a365ee
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  div rpow le inv pow 11dc30a365ee construction uses the P2 M Formalism Main Notions Bridge Lemma  div rpow le inv pow 11dc30a365ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsOneA.lean#L5-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsOneA.lean#L5-L33

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsOneA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂

theorem P2M_Formalism_MainNotions_BridgeLemma__div_rpow_le_inv_pow_11dc30a365ee {k r : ℕ} {C δ : ℝ} (hk : 1 ≤ k) (hC : 1 ≤ C) (hδ : δ ≤ 1 / 4) (hCk : C ^ 3 ≤ k) :
    (C / k) ^ (2 * (r : ℝ) * (1 - δ)) ≤ ((k : ℝ) ^ r)⁻¹ := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«div_rpow_le_inv_pow» := P2M_Formalism_MainNotions_BridgeLemma__div_rpow_le_inv_pow_11dc30a365ee
