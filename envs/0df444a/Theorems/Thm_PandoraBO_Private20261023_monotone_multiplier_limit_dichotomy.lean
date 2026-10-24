-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_monotone_multiplier_limit_dichotomy
-- name    : PandoraBO.Private20261023.monotone_multiplier_limit_dichotomy
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:29:29.302401+00:00
-- url     : https://prove2.me/theorems/46f4146f-9f97-430a-a3ef-16a145001830
-- title:
--   A monotone multiplier sequence approaches strictly from one side or is eventually constant
-- statement:
--   A convergent monotone real sequence either lies strictly below its limit and is nondecreasing, lies strictly above its limit and is nonincreasing, or equals its limit from some index onward. This separates the one-sided threshold cases from the eventual plateau case.
-- source:
--   Elementary auxiliary convergence dichotomy used in the finite-table formalization of the multiplier-limit argument.

import Definitions.Def_PandoraBO_Model
import Mathlib.Topology.Order.MonotoneConvergence
open Filter Topology
set_option autoImplicit false

theorem PandoraBO.Private20261023.monotone_multiplier_limit_dichotomy (multipliers : ℕ → ℝ) (limit : ℝ)
    (hmono : Monotone multipliers ∨ Antitone multipliers)
    (hlim : Tendsto multipliers atTop (𝓝 limit)) :
    (Monotone multipliers ∧ ∀ k, multipliers k < limit) ∨
    (Antitone multipliers ∧ ∀ k, limit < multipliers k) ∨
    ∃ K : ℕ, ∀ k, K ≤ k → multipliers k = limit  := by sorry
