-- Prove2me | Theorems.Thm_P2M_GlobalTheory_HermFrame_curv_blockDiagonal__429244f97e4b
-- name    : P2M_GlobalTheory_HermFrame_curv_blockDiagonal__429244f97e4b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:15.676829+00:00
-- url     : https://prove2.me/theorems/bee4d1cb-8357-5b49-96d3-eaf2d10b29bd
-- title:
--   P2 M Global Theory Herm Frame curv block Diagonal  429244f97e4b: P2 M Global Theory Herm Frame curv block Diagonal  429244f97e4b
-- statement:
--   The P2 M Global Theory Herm Frame curv block Diagonal  429244f97e4b construction uses the P2 M Global Theory Herm Frame curv block Diagonal  429244f97e4b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L140-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OpNormLeOpNormBlockDiagonal.lean#L140-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OpNormLeOpNormBlockDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
noncomputable section
open GlobalTheory GlobalTheory.HermFrame
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]
variable {o : Type*} [DecidableEq o] {m m' : o → Type*}
variable [Fintype o] [∀ i, Fintype (m i)] [∀ i, Fintype (m' i)]
variable [∀ i, DecidableEq (m i)] {H : ∀ i, E → Matrix (m i) (m i) ℂ} {z : E}

theorem P2M_GlobalTheory_HermFrame_curv_blockDiagonal__429244f97e4b {k : WithTop ℕ∞} (d : ∀ i, MContDiffAt k (H i) z)
    (h : ∀ i, IsUnit (H i z).det) (ξ η : E) :
    curv (fun x => blockDiagonal' fun i => H i x) z ξ η =
      blockDiagonal' fun i => curv (H i) z ξ η := by sorry

alias «GlobalTheory».«HermFrame».«curv_blockDiagonal'» := P2M_GlobalTheory_HermFrame_curv_blockDiagonal__429244f97e4b
