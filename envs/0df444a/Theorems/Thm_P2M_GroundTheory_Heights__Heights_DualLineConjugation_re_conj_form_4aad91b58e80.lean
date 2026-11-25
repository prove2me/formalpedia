-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineConjugation_re_conj_form_4aad91b58e80
-- name    : P2M_GroundTheory_Heights__Heights_DualLineConjugation_re_conj_form_4aad91b58e80
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:12.467286+00:00
-- url     : https://prove2.me/theorems/45026b5f-9164-43c8-8a53-e955f03e3d95
-- title:
--   P2 M Ground Theory Heights  Heights Dual Line Conjugation re conj form 4aad91b58e80: P2 M Ground Theory Heights  Heights Dual Line Conjugation re conj form 4aad91b58e80
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Line Conjugation re conj form 4aad91b58e80 construction uses the P2 M Ground Theory Heights  Heights Dual Line Conjugation re conj form 4aad91b58e80 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineConj.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineConj.lean#L39-L44

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

theorem P2M_GroundTheory_Heights__Heights_DualLineConjugation_re_conj_form_4aad91b58e80 {n : Type} [Fintype n] (H : Matrix n n ℂ) (v : n → ℂ) :
    (star (fun j => starRingEnd ℂ (v j)) ⬝ᵥ (H *ᵥ fun j => starRingEnd ℂ (v j))).re =
      (star v ⬝ᵥ (H.map (starRingEnd ℂ) *ᵥ v)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualLineConjugation».«re_conj_form» := P2M_GroundTheory_Heights__Heights_DualLineConjugation_re_conj_form_4aad91b58e80
