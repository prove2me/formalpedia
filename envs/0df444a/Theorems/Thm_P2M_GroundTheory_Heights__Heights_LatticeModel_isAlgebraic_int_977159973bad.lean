-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_isAlgebraic_int_977159973bad
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_isAlgebraic_int_977159973bad
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:26.334705+00:00
-- url     : https://prove2.me/theorems/f737bb16-f92c-4dd0-85d4-ca0330a1b66a
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model is Algebraic int 977159973bad: P2 M Ground Theory Heights  Heights Lattice Model is Algebraic int 977159973bad
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model is Algebraic int 977159973bad construction uses the P2 M Ground Theory Heights  Heights Lattice Model is Algebraic int 977159973bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L17-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockModelA
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.LatticeModel
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_isAlgebraic_int_977159973bad (x : K) : IsAlgebraic ℤ x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«isAlgebraic_int» := P2M_GroundTheory_Heights__Heights_LatticeModel_isAlgebraic_int_977159973bad
