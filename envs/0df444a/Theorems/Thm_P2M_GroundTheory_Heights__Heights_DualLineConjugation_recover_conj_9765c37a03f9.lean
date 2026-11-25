-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineConjugation_recover_conj_9765c37a03f9
-- name    : P2M_GroundTheory_Heights__Heights_DualLineConjugation_recover_conj_9765c37a03f9
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:28.069424+00:00
-- url     : https://prove2.me/theorems/f7cb9002-60ed-5fe2-895f-a2cf9f79a9df
-- title:
--   P2 M Ground Theory Heights  Heights Dual Line Conjugation recover conj 9765c37a03f9: P2 M Ground Theory Heights  Heights Dual Line Conjugation recover conj 9765c37a03f9
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Line Conjugation recover conj 9765c37a03f9 construction uses the P2 M Ground Theory Heights  Heights Dual Line Conjugation recover conj 9765c37a03f9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineConj.lean#L29-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineConj.lean#L29-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField NumberField.ComplexEmbedding
noncomputable section
open GroundTheory.Heights₂.Heights.DualLineConjugation
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i}
  {T : Type} [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_DualLineConjugation_recover_conj_9765c37a03f9 (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualRecover b hb (fun t => starRingEnd ℂ (z t)) =
      fun p => starRingEnd ℂ (dualRecover b hb z (conjugate p.1, p.2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualLineConjugation».«recover_conj» := P2M_GroundTheory_Heights__Heights_DualLineConjugation_recover_conj_9765c37a03f9
