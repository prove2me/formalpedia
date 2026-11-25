-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_linearCombination_eq_zero_1e4dd3352d12
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_linearCombination_eq_zero_1e4dd3352d12
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:06.797405+00:00
-- url     : https://prove2.me/theorems/63669491-9825-454e-9221-203a0dbd40cc
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines linear Combination eq zero 1e4dd3352d12: P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines linear Combination eq z
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines linear Combination eq zero 1e4dd3352d12 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines linear Combination eq zero 1e4dd3352d12 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PGramDetermines.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PGramDetermines.lean#L42-L49

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_linearCombination_eq_zero_1e4dd3352d12 (h : HermitianForm F E W) {n : ℕ} {e e' : Fin n → W}
    (hL' : IsLattice E (AddSubgroup.closure (Set.range e')))
    (hG : ∀ a b, h.toSesq (e a) (e b) = h.toSesq (e' a) (e' b)) (c : Fin n → E)
    (hc : Fintype.linearCombination E e c = 0) : Fintype.linearCombination E e' c = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GramDetermines».«linearCombination_eq_zero» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_linearCombination_eq_zero_1e4dd3352d12
