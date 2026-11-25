-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_sesq_swap_9b7db62729c5
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_sesq_swap_9b7db62729c5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:51:34.414561+00:00
-- url     : https://prove2.me/theorems/1b7c6002-e217-47b1-844b-d4947dee48e1
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive sesq swap 9b7db62729c5: P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive sesq swap 9b7db627
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive sesq swap 9b7db62729c5 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Hyperbolic Pair Transitive sesq swap 9b7db62729c5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHyperbolicPairTransitive.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PHyperbolicPairTransitive.lean#L18-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHyperbolicPairTransitive
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
variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
open GroundTheory.Heights₂.Heights.FiniteCovolume.HyperbolicPairTransitive
omit [NumberField E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_sesq_swap_9b7db62729c5 (h : HermitianForm F E W) (x y : W) :
    h.toSesq y x = conj F E (h.toSesq x y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«HyperbolicPairTransitive».«sesq_swap» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_HyperbolicPairTransitive_sesq_swap_9b7db62729c5
