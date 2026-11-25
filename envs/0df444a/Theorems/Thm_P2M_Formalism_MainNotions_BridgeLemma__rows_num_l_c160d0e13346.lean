-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rows_num_l_c160d0e13346
-- name    : P2M_Formalism_MainNotions_BridgeLemma__rows_num_l_c160d0e13346
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:07.651698+00:00
-- url     : https://prove2.me/theorems/62c0d9e5-7f3d-4c33-bc0e-50a75c3451e3
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  rows num l c160d0e13346: P2 M Formalism Main Notions Bridge Lemma  rows num l c160d0e13346
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  rows num l c160d0e13346 construction uses the P2 M Formalism Main Notions Bridge Lemma  rows num l c160d0e13346 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsNum.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsNum.lean#L9-L30

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂

theorem P2M_Formalism_MainNotions_BridgeLemma__rows_num_l_c160d0e13346 {P σ h cr Γ a2 dq : ℝ} (hP : 1 ≤ P) (hσ : 1 ≤ σ) (h1 : 1 ≤ h) (hh : h ≤ P * σ ^ 4)
    (hcr : 0 ≤ cr) (hΓ : 0 ≤ Γ) :
    (h ^ cr) ^ 2 * (Γ * σ ^ a2) * σ ^ (-dq) ≤ (P ^ cr) ^ 2 * Γ * σ ^ (8 * cr + a2 - dq) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«rows_num_l» := P2M_Formalism_MainNotions_BridgeLemma__rows_num_l_c160d0e13346
