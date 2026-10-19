-- Prove2me | Theorems.Thm_PackingBounds_fullQuotientRootSet_eq_radial
-- name    : PackingBounds.fullQuotientRootSet_eq_radial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:57:05.603159+00:00
-- url     : https://prove2.me/theorems/d844523d-9d47-44e7-9435-4aef56202349
-- title:
--   PackingBounds.fullQuotientRootSet_eq_radial
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
set_option maxHeartbeats 1600000
noncomputable section
open Filter
open scoped Topology
open PackingBounds

theorem PackingBounds.fullQuotientRootSet_eq_radial (d : ℕ) :
    {q : ℝ | ∃ f : FullAdmissible d,
      fullQuotient f ^ ((d : ℝ)⁻¹) = q} =
      {q : ℝ | ∃ f : CohnElkies.Admissible d,
        CohnElkies.quotient f ^ ((d : ℝ)⁻¹) = q} := by sorry
