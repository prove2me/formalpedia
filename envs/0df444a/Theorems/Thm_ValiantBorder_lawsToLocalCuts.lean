-- Prove2me | Theorems.Thm_ValiantBorder_lawsToLocalCuts
-- name    : ValiantBorder.lawsToLocalCuts
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:06:45.499697+00:00
-- url     : https://prove2.me/theorems/0e61f4de-c67e-44df-a9ad-12549af8f82b
-- title:
--   From exchange laws to local cut programs
-- statement:
--   Let the coefficient ring be finitely generated over the integers. A family of exchange laws on the unitriangular group of height $h≥3$ satisfying $1+8C_1≤h/4$ yields finitely supported program weights for which the local cuts exist.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Cuts.lean#L72-L113).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Cuts.lean#L72-L113.

import Definitions.Def_ValiantBorder_cutLaws
import Definitions.Def_ValiantBorder_localCuts

theorem ValiantBorder.lawsToLocalCuts {A : Type} [CommRing A] [Algebra.FiniteType ℤ A] {h : ℕ} [NeZero h]
    (VL : Nc.Tow.VLaws A (Nc.Vp.cNear (h := h)) (Nc.Vp.dNear (h := h)) 1 (2 ^ Nc.Tower.ee h))
    (h3 : 3 ≤ h) (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ θ : List Bool → A, (Function.support θ).Finite ∧ NS1.LocalCuts θ := by sorry
