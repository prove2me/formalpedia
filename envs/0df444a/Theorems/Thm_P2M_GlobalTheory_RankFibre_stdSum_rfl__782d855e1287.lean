-- Prove2me | Theorems.Thm_P2M_GlobalTheory_RankFibre_stdSum_rfl__782d855e1287
-- name    : P2M_GlobalTheory_RankFibre_stdSum_rfl__782d855e1287
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:20.959319+00:00
-- url     : https://prove2.me/theorems/d335a5b3-3a18-4f13-9dc4-1c307ab49dbb
-- title:
--   P2 M Global Theory Rank Fibre std Sum rfl  782d855e1287: P2 M Global Theory Rank Fibre std Sum rfl  782d855e1287
-- statement:
--   The P2 M Global Theory Rank Fibre std Sum rfl  782d855e1287 construction uses the P2 M Global Theory Rank Fibre std Sum rfl  782d855e1287 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreMemInducedSpace.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FibreMemInducedSpace.lean#L15-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FibreMemInducedSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.WeilM
open GlobalTheory GlobalTheory.RankFibre
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
local notation:70 M:70 " ⬝ₘ " N:71 => HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid) M N

theorem P2M_GlobalTheory_RankFibre_stdSum_rfl__782d855e1287 (a b : ℕ) : stdSum (rfl : a + b = a + b) = finSumFinEquiv := by sorry

alias «GlobalTheory».«RankFibre».«stdSum_rfl'» := P2M_GlobalTheory_RankFibre_stdSum_rfl__782d855e1287
