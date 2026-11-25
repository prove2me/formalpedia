-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_card_infinitePlace_eq_4816e5c7e85e
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_card_infinitePlace_eq_4816e5c7e85e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:55:01.300651+00:00
-- url     : https://prove2.me/theorems/4d069a98-4ec3-4d8d-8757-8e06dc75cc62
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume card infinite Place eq 4816e5c7e85e: P2 M Ground Theory Heights  Heights Finite Covolume card infinite Place eq 4816e5c7e85e
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume card infinite Place eq 4816e5c7e85e construction uses the P2 M Ground Theory Heights  Heights Finite Covolume card infinite Place eq 4816e5c7e85e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PImaginaryLatticeCocompact.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PImaginaryLatticeCocompact.lean#L45-L51

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
omit [IsTotallyReal F]
variable (F E)

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_card_infinitePlace_eq_4816e5c7e85e : Fintype.card (InfinitePlace E) = finrank ℚ F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«card_infinitePlace_eq» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_card_infinitePlace_eq_4816e5c7e85e
