-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DetBound__Multi_eq_det_smul_70a319abcdeb
-- name    : P2M_GlobalTheory_DetBound__Multi_eq_det_smul_70a319abcdeb
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:06:07.75747+00:00
-- url     : https://prove2.me/theorems/9b2f7f4b-82ae-4215-a6cb-a89e3553fe49
-- title:
--   P2 M Global Theory Det Bound  Multi eq det smul 70a319abcdeb: P2 M Global Theory Det Bound  Multi eq det smul 70a319abcdeb
-- statement:
--   The P2 M Global Theory Det Bound  Multi eq det smul 70a319abcdeb construction uses the P2 M Global Theory Det Bound  Multi eq det smul 70a319abcdeb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodTraceIntegral.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodTraceIntegral.lean#L12-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodTraceIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.DetBound
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations

theorem P2M_GlobalTheory_DetBound__Multi_eq_det_smul_70a319abcdeb {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {n : ℕ}
    (b : Module.Basis (Fin n) O M) (v : Fin n → M) :
    exteriorPower.ιMulti O n v = b.det v • exteriorPower.ιMulti O n b := by sorry

alias «GlobalTheory».«DetBound».«ιMulti_eq_det_smul» := P2M_GlobalTheory_DetBound__Multi_eq_det_smul_70a319abcdeb
