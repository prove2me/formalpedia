-- Prove2me | Theorems.Thm_P2M_Formalism_REAL_mem_kSpan_self__eef759b81251
-- name    : P2M_Formalism_REAL_mem_kSpan_self__eef759b81251
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:55.703742+00:00
-- url     : https://prove2.me/theorems/0876ffe6-b11c-4d30-b528-92dc17baa998
-- title:
--   P2 M Formalism REAL mem k Span self  eef759b81251: P2 M Formalism REAL mem k Span self  eef759b81251
-- statement:
--   The P2 M Formalism REAL mem k Span self  eef759b81251 construction uses the P2 M Formalism REAL mem k Span self  eef759b81251 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L15-L17

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)

theorem P2M_Formalism_REAL_mem_kSpan_self__eef759b81251 : u ∈ kSpan ε E u := by sorry

alias «Formalism».«REAL».«mem_kSpan_self'» := P2M_Formalism_REAL_mem_kSpan_self__eef759b81251
