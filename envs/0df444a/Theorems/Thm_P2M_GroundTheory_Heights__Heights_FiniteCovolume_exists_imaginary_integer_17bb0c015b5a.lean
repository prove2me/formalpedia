-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_imaginary_integer_17bb0c015b5a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_imaginary_integer_17bb0c015b5a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:09:48.384383+00:00
-- url     : https://prove2.me/theorems/5d187173-216d-412b-901a-66c8dda70a34
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume exists imaginary integer 17bb0c015b5a: P2 M Ground Theory Heights  Heights Finite Covolume exists imaginary integer 17bb0c015b5a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume exists imaginary integer 17bb0c015b5a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume exists imaginary integer 17bb0c015b5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PImaginaryLatticeCocompact.lean#L21-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PImaginaryLatticeCocompact.lean#L21-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StImaginaryLatticeCocompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PImaginaryLatticeCocompact
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
omit [IsTotallyReal F] [IsTotallyComplex E]
variable (F E)

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_imaginary_integer_17bb0c015b5a : ∃ t : 𝓞 E, (t : E) ≠ 0 ∧ conj F E (t : E) = -(t : E) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«exists_imaginary_integer» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_imaginary_integer_17bb0c015b5a
