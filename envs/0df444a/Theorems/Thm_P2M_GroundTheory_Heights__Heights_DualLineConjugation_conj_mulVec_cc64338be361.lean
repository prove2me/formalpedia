-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DualLineConjugation_conj_mulVec_cc64338be361
-- name    : P2M_GroundTheory_Heights__Heights_DualLineConjugation_conj_mulVec_cc64338be361
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:53.730855+00:00
-- url     : https://prove2.me/theorems/d99da162-e5ec-40ea-8a68-4edc144e9385
-- title:
--   P2 M Ground Theory Heights  Heights Dual Line Conjugation conj mul Vec cc64338be361: P2 M Ground Theory Heights  Heights Dual Line Conjugation conj mul Vec cc64338be361
-- statement:
--   The P2 M Ground Theory Heights  Heights Dual Line Conjugation conj mul Vec cc64338be361 construction uses the P2 M Ground Theory Heights  Heights Dual Line Conjugation conj mul Vec cc64338be361 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineConj.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineConj.lean#L21-L27

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
omit [Fintype T] [DecidableEq T]

theorem P2M_GroundTheory_Heights__Heights_DualLineConjugation_conj_mulVec_cc64338be361 (b : Module.Basis T ℤ (dualLattice F)) (w : (K →+* ℂ) × Fin i → ℂ) :
    (fun t => starRingEnd ℂ ((dualEmbMatrix b *ᵥ w) t)) =
      dualEmbMatrix b *ᵥ fun p => starRingEnd ℂ (w (conjugate p.1, p.2)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DualLineConjugation».«conj_mulVec» := P2M_GroundTheory_Heights__Heights_DualLineConjugation_conj_mulVec_cc64338be361
