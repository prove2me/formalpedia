-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__rows_fibres_f4031f5b82c0
-- name    : P2M_Formalism_MainNotions_BridgeLemma__rows_fibres_f4031f5b82c0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:06:58.116136+00:00
-- url     : https://prove2.me/theorems/fa05e427-bc57-4b2a-9b57-0132a41207a7
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  rows fibres f4031f5b82c0: P2 M Formalism Main Notions Bridge Lemma  rows fibres f4031f5b82c0
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  rows fibres f4031f5b82c0 construction uses the P2 M Formalism Main Notions Bridge Lemma  rows fibres f4031f5b82c0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsFibres.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/RowsFibres.lean#L10-L18

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsRpowPow
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_RowsFibres
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
open Classical

theorem P2M_Formalism_MainNotions_BridgeLemma__rows_fibres_f4031f5b82c0 {Pr κ : Type} (S : Finset Pr) (c₁ c₂ : Pr → κ) (F : Pr → ℝ) :
    ∑ p ∈ S, F p = ∑ x ∈ S.image c₁, ∑ y ∈ S.image c₂, ∑ p ∈ S.filter (fun p => c₁ p = x ∧ c₂ p = y), F p := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«rows_fibres» := P2M_Formalism_MainNotions_BridgeLemma__rows_fibres_f4031f5b82c0
