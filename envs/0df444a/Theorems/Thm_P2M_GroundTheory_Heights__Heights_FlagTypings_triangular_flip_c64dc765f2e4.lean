-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FlagTypings_triangular_flip_c64dc765f2e4
-- name    : P2M_GroundTheory_Heights__Heights_FlagTypings_triangular_flip_c64dc765f2e4
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:34:10.518913+00:00
-- url     : https://prove2.me/theorems/4ef10e66-1329-4a12-9e6e-6da9bdc6746d
-- title:
--   P2 M Ground Theory Heights  Heights Flag Typings triangular flip c64dc765f2e4: P2 M Ground Theory Heights  Heights Flag Typings triangular flip c64dc765f2e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Flag Typings triangular flip c64dc765f2e4 construction uses the P2 M Ground Theory Heights  Heights Flag Typings triangular flip c64dc765f2e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L85-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/IsVerticalDivOfIsVerticalDivisor.lean#L85-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FlagTypings
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {Ω : Type*} [Field Ω] {E : Type*} [AddCommGroup E] [Module Ω E] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_FlagTypings_triangular_flip_c64dc765f2e4 (w w' : Module.Basis (Fin N) Ω E)
    (h : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0) :
    (∀ i j : Fin N, i < j → w'.repr (w i) j = 0) ∧ ∀ i, w.repr (w' i) i ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FlagTypings».«triangular_flip» := P2M_GroundTheory_Heights__Heights_FlagTypings_triangular_flip_c64dc765f2e4
