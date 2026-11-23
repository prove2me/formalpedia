-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rows_rpow_pow_7d3f75c3e74b
-- name    : P2M_Formalism_MainNotions_BridgeLemma__rows_rpow_pow_7d3f75c3e74b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:14.924805+00:00
-- url     : https://prove2.me/theorems/9a941623-3b03-4f61-a5af-5b45347a36ab
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  rows rpow pow 7d3f75c3e74b: P2 M Formalism Main Notions Bridge Lemma  rows rpow pow 7d3f75c3e74b
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  rows rpow pow 7d3f75c3e74b construction uses the P2 M Formalism Main Notions Bridge Lemma  rows rpow pow 7d3f75c3e74b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsRpowPow.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsRpowPow.lean#L8-L11

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsNum
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsRpowPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open Formalism.HermitianLatticeCounting

theorem P2M_Formalism_MainNotions_BridgeLemma__rows_rpow_pow_7d3f75c3e74b {b : ℝ} (hb : 0 < b) (x : ℝ) (n : ℕ) : (b ^ x) ^ n = b ^ (x * n) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«rows_rpow_pow» := P2M_Formalism_MainNotions_BridgeLemma__rows_rpow_pow_7d3f75c3e74b
