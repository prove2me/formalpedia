-- Prove2me | Theorems.Thm_SmoothJordanDomain_exists_pos_radius_closure_subset_ball
-- name    : SmoothJordanDomain.exists_pos_radius_closure_subset_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:47.313064+00:00
-- url     : https://prove2.me/theorems/b3038747-beff-5462-827b-6e762b9cc857
-- title:
--   Smooth Jordan Domain: exists pos radius closure subset ball
-- statement:
--   Around any chosen center, the closed carrier of a smooth Jordan domain is
--   contained in a ball of some positive radius.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCompact.lean#L41-L44
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCompact.lean#L41-L44

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_SmoothJordanCompact
set_option autoImplicit false
open Complex Metric Set

theorem SmoothJordanDomain.exists_pos_radius_closure_subset_ball
    (Omega : SmoothJordanDomain) (c : ℂ) :
    ∃ R : ℝ, 0 < R ∧ closure Omega.carrier ⊆ Metric.ball c R := by sorry
