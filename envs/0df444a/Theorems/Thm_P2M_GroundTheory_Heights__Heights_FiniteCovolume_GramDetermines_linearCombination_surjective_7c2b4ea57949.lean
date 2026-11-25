-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_linearCombination_surjective_7c2b4ea57949
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_linearCombination_surjective_7c2b4ea57949
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:43:52.429049+00:00
-- url     : https://prove2.me/theorems/48fcc02e-a889-574d-9047-c07c8ff6a30b
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines linear Combination surjective 7c2b4ea57949: P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines linear Combination s
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines linear Combination surjective 7c2b4ea57949 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Gram Determines linear Combination surjective 7c2b4ea57949 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PGramDetermines.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PGramDetermines.lean#L28-L38

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
omit [NumberField E] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_linearCombination_surjective_7c2b4ea57949 {n : ℕ} {e : Fin n → W}
    (hL : IsLattice E (AddSubgroup.closure (Set.range e))) :
    Function.Surjective (Fintype.linearCombination E e) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«GramDetermines».«linearCombination_surjective» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_GramDetermines_linearCombination_surjective_7c2b4ea57949
