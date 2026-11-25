-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_sesq_linearCombination_780dd4cdbdca
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_sesq_linearCombination_780dd4cdbdca
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:25:44.710791+00:00
-- url     : https://prove2.me/theorems/8b4e2369-3e7c-414e-94ba-8e8ee6498ee8
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines sesq linear Combination 780dd4cdbdca: P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines sesq linear Combination 78
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines sesq linear Combination 780dd4cdbdca construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines sesq linear Combination 780dd4cdbdca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PGramDetermines.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PGramDetermines.lean#L19-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StGramDetermines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramDetermines
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.GramDetermines
omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_sesq_linearCombination_780dd4cdbdca (h : HermitianForm F E W) {n : ℕ} {e e' : Fin n → W}
    (hG : ∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) (c d : Fin n → E) :
    h.toSesq (Fintype.linearCombination E e' c) (Fintype.linearCombination E e' d) =
      h.toSesq (Fintype.linearCombination E e c) (Fintype.linearCombination E e d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GramDetermines».«sesq_linearCombination» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_sesq_linearCombination_780dd4cdbdca
