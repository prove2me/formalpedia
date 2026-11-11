-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_proposition_4_4
-- name    : TwoItemMenu1393.Main.proposition_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:27.242776+00:00
-- url     : https://prove2.me/theorems/2572a0a9-dae2-4d54-9c0a-289eff977ad8
-- title:
--   Proposition 4.4 — Uniform loss for small menus
-- statement:
--   There are positive constants $c_{\mathrm{menu}},c_{\mathrm{loss}},h_0$ such that for every $0<h<h_0$ and every admissible mechanism with menu size strictly less than $c_{\mathrm{menu}}h^{-2}$,
--   $$\mathrm{Rev}_{F_h}(u,g)\le\mathrm{OPT}(F_h)-c_{\mathrm{loss}}h.$$
--   The distribution is the explicit completed family of Proposition 4.1. Competitors range over all admissible mechanisms and all Borel selections; finite menu size counts every actual selected outcome. No full-cell selection condition is imposed on competitors. This uniform threshold is the direct lower-bound input to Theorem 1.2.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: Borel probability laws on the type square → ambient Borel measures with total mass one and zero mass off the square; reason: pushforward along the square inclusion gives precisely the same laws and integrals
--   - encoding: nonnegative integer menu sizes with possible infinity → infima and suprema of natural numbers embedded in ℝ≥0∞; reason: empty feasible sets retain infinity and zero-size menus remain allowed
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Proposition 4.4, p. 13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=13

import Definitions.Def_TwoItemMenu1393_Main_Distribution
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Proposition 4.4, p. 13.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem proposition_4_4 :
    ∃ cm cl h₀ : ℝ, 0 < cm ∧ 0 < cl ∧ 0 < h₀ ∧
      ∀ (h : ℝ) (M : Mechanism), 0 < h → h < h₀ → Admissible M →
        menuSize M < ENNReal.ofReal (cm/h^2) →
        revenue (lowerLaw h) M ≤ optimum (lowerLaw h) - cl*h := by sorry

end TwoItemMenu1393.Main
