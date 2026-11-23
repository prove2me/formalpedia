-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rows_num_Q_8db4989c427f
-- name    : P2M_Formalism_MainNotions_BridgeLemma__rows_num_Q_8db4989c427f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:18.251817+00:00
-- url     : https://prove2.me/theorems/8897834e-6ec0-4371-b1cb-a1f0c5ede1db
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  rows num Q 8db4989c427f: P2 M Formalism Main Notions Bridge Lemma  rows num Q 8db4989c427f
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  rows num Q 8db4989c427f construction uses the P2 M Formalism Main Notions Bridge Lemma  rows num Q 8db4989c427f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsRpowPow.lean#L13-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsRpowPow.lean#L13-L58

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

theorem P2M_Formalism_MainNotions_BridgeLemma__rows_num_Q_8db4989c427f {f r : ℕ} {b pe E1 cr δ : ℝ} (hb : 2 ≤ b) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) :
    (1 + δ) * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2) * ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2 ≤
      b ^ (1 + 12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + pe * (2 * E1 + 2 * cr + 6 * ((r : ℝ) + 1) ^ 2)) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«rows_num_Q» := P2M_Formalism_MainNotions_BridgeLemma__rows_num_Q_8db4989c427f
