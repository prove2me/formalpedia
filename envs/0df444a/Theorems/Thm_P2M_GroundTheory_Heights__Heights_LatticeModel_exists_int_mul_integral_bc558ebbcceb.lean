-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_mul_integral_bc558ebbcceb
-- name    : P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_mul_integral_bc558ebbcceb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:31.66581+00:00
-- url     : https://prove2.me/theorems/49ad43ad-93f1-425d-8881-65c89d9bc399
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Model exists int mul integral bc558ebbcceb: P2 M Ground Theory Heights  Heights Lattice Model exists int mul integral bc558ebbcceb
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Model exists int mul integral bc558ebbcceb construction uses the P2 M Ground Theory Heights  Heights Lattice Model exists int mul integral bc558ebbcceb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockModelA.lean#L20-L23

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

theorem P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_mul_integral_bc558ebbcceb (x : K) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = n * x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeModel».«exists_int_mul_integral» := P2M_GroundTheory_Heights__Heights_LatticeModel_exists_int_mul_integral_bc558ebbcceb
