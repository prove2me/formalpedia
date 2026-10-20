-- Prove2me | Theorems.Thm_SoficGroups_KunRootedWordPower_pairedDefectWordAverage_eq_unitaryFinsetMarkov_iterate
-- name    : SoficGroups.KunRootedWordPower.pairedDefectWordAverage_eq_unitaryFinsetMarkov_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/b98afaef-eca9-4833-bfe2-243519833dae
-- title:
--   SoficGroups.KunRootedWordPower.pairedDefectWordAverage_eq_unitaryFinsetMarkov_iterate
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

theorem SoficGroups.KunRootedWordPower.pairedDefectWordAverage_eq_unitaryFinsetMarkov_iterate
    {G H : Type*} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : SoficGroups.UnitaryRepresentation G H)
    (S : Finset G) (v : G × G → H)
    (hequivariant : ∀ a g h : G,
      π a (v (g, h)) = v (a * g, a * h))
    (k : ℕ) :
    pairedDefectWordAverage (fun i : ↥S => (i : G)) v k =
      ((unitaryFinsetMarkov π S)^[k])
        (pairedDefectWordAverage (fun i : ↥S => (i : G)) v 0) := by sorry
