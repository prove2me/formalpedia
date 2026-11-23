-- Prove2me | Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_TW_Idx_ord_ne_top__57ca83d61db5
-- name    : P2M_Formalism_IrreducibleCountingLemmas_TW_Idx_ord_ne_top__57ca83d61db5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:37.051571+00:00
-- url     : https://prove2.me/theorems/503b5fb1-f3ea-4e50-8325-1004477c7463
-- title:
--   P2 M Formalism Irreducible Counting Lemmas TW Idx ord ne top  57ca83d61db5: P2 M Formalism Irreducible Counting Lemmas TW Idx ord ne top  57ca83d61db5
-- statement:
--   The P2 M Formalism Irreducible Counting Lemmas TW Idx ord ne top  57ca83d61db5 construction uses the P2 M Formalism Irreducible Counting Lemmas TW Idx ord ne top  57ca83d61db5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L169-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWIndexAdditive.lean#L169-L173

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.Idx
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]

theorem P2M_Formalism_IrreducibleCountingLemmas_TW_Idx_ord_ne_top__57ca83d61db5 {D : O} (hD : D ≠ 0) : Ring.ord O D ≠ ⊤ := by sorry

alias «Formalism».«IrreducibleCountingLemmas».«TW».«Idx».«ord_ne_top'» := P2M_Formalism_IrreducibleCountingLemmas_TW_Idx_ord_ne_top__57ca83d61db5
