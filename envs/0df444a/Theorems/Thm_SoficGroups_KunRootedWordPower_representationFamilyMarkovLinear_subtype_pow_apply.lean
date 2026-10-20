-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_representationFamilyMarkovLinear_subtype_pow_apply
-- name    : SoficGroups.KunRootedWordPower.representationFamilyMarkovLinear_subtype_pow_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/66eaf003-be62-4736-8492-7d345d2b89ef
-- title:
--   SoficGroups.KunRootedWordPower.representationFamilyMarkovLinear_subtype_pow_apply
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w

theorem SoficGroups.KunRootedWordPower.representationFamilyMarkovLinear_subtype_pow_apply
    {G H : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : SoficGroups.UnitaryRepresentation G H)
    (S : Finset G) (k : ℕ) (x : H) :
    (representationFamilyMarkovLinear π
        (fun i : ↥S => (i : G)) ^ k) x =
      ((unitaryFinsetMarkov π S)^[k]) x := by sorry
