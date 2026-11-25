-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_mem_intMultiples_818cdd960c3a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_mem_intMultiples_818cdd960c3a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:36:41.999192+00:00
-- url     : https://prove2.me/theorems/c3595d72-ce27-49fe-8c49-961dae9e486f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form mem int Multiples 818cdd960c3a: P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form mem int Multiples 818cdd960c3a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form mem int Multiples 818cdd960c3a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Line Normal Form mem int Multiples 818cdd960c3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLineNormalForm.lean#L75-L76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PIdealClassesFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineCoeffsFG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsCommonMultiple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineNormalForm
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
open GroundTheory.Heights₂.Heights.FiniteCovolume.LineNormalForm
variable {E : Type*} [Field E] [NumberField E]
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_mem_intMultiples_818cdd960c3a {N : ℕ} {x : E} : x ∈ intMultiples E N ↔ IsIntegral ℤ ((N : E)⁻¹ * x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«LineNormalForm».«mem_intMultiples» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineNormalForm_mem_intMultiples_818cdd960c3a
