-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rows_num_nd_91742433f9a9
-- name    : P2M_Formalism_MainNotions_BridgeLemma__rows_num_nd_91742433f9a9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:15.716074+00:00
-- url     : https://prove2.me/theorems/dbf58d5f-ae61-446c-ab38-2e195d674900
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  rows num nd 91742433f9a9: P2 M Formalism Main Notions Bridge Lemma  rows num nd 91742433f9a9
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  rows num nd 91742433f9a9 construction uses the P2 M Formalism Main Notions Bridge Lemma  rows num nd 91742433f9a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsRpowPow.lean#L60-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsRpowPow.lean#L60-L106

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

theorem P2M_Formalism_MainNotions_BridgeLemma__rows_num_nd_91742433f9a9 {k m f s r : ℕ} {b g v Γ c C pe E1 cr δ rD XiP : ℝ} {Xi : ℕ → ℝ}
    (hb : 2 ≤ b) (hg : 0 < g) (hv : 0 < v) (hΓ : 0 ≤ Γ) (hc : 0 ≤ c) (hcC : c ≤ C) (hC : 1 ≤ C)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1) (hrD : 0 ≤ rD) (hXiP : 0 ≤ XiP) (hXi : XiP ≤ Xi s)
    (hexp : 1 + 12 * (f : ℝ) * ((r : ℝ) + 1) ^ 2 + pe * (2 * E1 + 2 * cr + 6 * ((r : ℝ) + 1) ^ 2) ≤
      C * (m : ℝ) ^ 2 * f * (C * ((s : ℝ) + m) * (m : ℝ) ^ 2)) :
    (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
        (XiP * (((b ^ pe) ^ E1) ^ 2 * ((b ^ pe) ^ cr) ^ 2 * (c * s * f) ^ (6 * s * f) * Γ)) * ((1 + δ) * rD) *
        ((41 ^ f * (b ^ pe) ^ 3) ^ ((r + 1) ^ 2)) ^ 2 ≤
      LatticeSumBounds.ndRow C k m f s b g v Γ Xi * rD := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«rows_num_nd» := P2M_Formalism_MainNotions_BridgeLemma__rows_num_nd_91742433f9a9
