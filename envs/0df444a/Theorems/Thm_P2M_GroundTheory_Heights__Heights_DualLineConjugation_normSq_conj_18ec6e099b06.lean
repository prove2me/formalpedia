-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineConjugation_normSq_conj_18ec6e099b06
-- name    : P2M_GroundTheory_Heights__Heights_DualLineConjugation_normSq_conj_18ec6e099b06
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:22.019968+00:00
-- url     : https://prove2.me/theorems/9c646961-fc8d-4788-91e1-554168679dc1
-- title:
--   P2 M Ground Theory Heights  Heights Dual Line Conjugation norm Sq conj 18ec6e099b06: P2 M Ground Theory Heights  Heights Dual Line Conjugation norm Sq conj 18ec6e099b06
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Line Conjugation norm Sq conj 18ec6e099b06 construction uses the P2 M Ground Theory Heights  Heights Dual Line Conjugation norm Sq conj 18ec6e099b06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineConj.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineConj.lean#L46-L54

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

theorem P2M_GroundTheory_Heights__Heights_DualLineConjugation_normSq_conj_18ec6e099b06 (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (z : T → ℂ) :
    dualNormSq b hb (fun t => starRingEnd ℂ (z t)) = dualNormSq b hb z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualLineConjugation».«normSq_conj» := P2M_GroundTheory_Heights__Heights_DualLineConjugation_normSq_conj_18ec6e099b06
