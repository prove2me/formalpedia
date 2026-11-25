-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rpow_le_rpow_mul_rpow_133b1c2bea84
-- name    : P2M_Formalism_MainNotions_BridgeLemma__rpow_le_rpow_mul_rpow_133b1c2bea84
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:11.022782+00:00
-- url     : https://prove2.me/theorems/fd2dfd1f-4953-4c74-b15a-85fe57d583b4
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  rpow le rpow mul rpow 133b1c2bea84: P2 M Formalism Main Notions Bridge Lemma  rpow le rpow mul rpow 133b1c2bea84
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  rpow le rpow mul rpow 133b1c2bea84 construction uses the P2 M Formalism Main Notions Bridge Lemma  rpow le rpow mul rpow 133b1c2bea84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsOneN.lean#L5-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsOneN.lean#L5-L12

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsNum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsOneN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂

theorem P2M_Formalism_MainNotions_BridgeLemma__rpow_le_rpow_mul_rpow_133b1c2bea84 {P σ h c : ℝ} (hP : 1 ≤ P) (hσ : 1 ≤ σ) (h1 : 1 ≤ h) (hh : h ≤ P * σ ^ 4) (hc : 0 ≤ c) :
    h ^ c ≤ P ^ c * σ ^ (4 * c) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«rpow_le_rpow_mul_rpow» := P2M_Formalism_MainNotions_BridgeLemma__rpow_le_rpow_mul_rpow_133b1c2bea84
