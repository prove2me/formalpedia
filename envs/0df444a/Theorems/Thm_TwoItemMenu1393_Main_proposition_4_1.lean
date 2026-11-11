-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_proposition_4_1
-- name    : TwoItemMenu1393.Main.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:02.100086+00:00
-- url     : https://prove2.me/theorems/adc64266-ef4b-4352-87de-94d910148cf6
-- title:
--   Proposition 4.1 — Atomic distribution and loss certificate
-- statement:
--   For all sufficiently small positive $h$, the completed measure $F_h$ is a finitely supported Borel probability law on $[0,1]^2$, and the quadratic menu $U_h$ with the fixed highest-price selection $g^*$ is admissible and optimal. There is one positive constant $c_{\mathrm{cert}}$, independent of $h$ and every competing mechanism, such that
--   $$L_h(u,g)\ge c_{\mathrm{cert}}h\sum_H D_H(u,g),\qquad L_h(u,g)\ge c_{\mathrm{cert}}u(s_i^h),\qquad L_h(u,g)\ge c_{\mathrm{cert}}\sum_{j=1}^2(1-g_j(b_i^h)).$$
--   The sum is over all full cells; both anchor inequalities hold for each of the three anchors. Here $D_H$ is the sum of exactly eight IC slacks and $L_h$ is optimal revenue minus the competitor's revenue. All inequalities use the actual selected allocations, including ties. This is the lower-bound loss certificate.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: Borel probability laws on the type square → ambient Borel measures with total mass one and zero mass off the square; reason: pushforward along the square inclusion gives precisely the same laws and integrals
--   - encoding: the distribution supplied by the radial construction → the explicitly defined normalized measure lowerLaw h; reason: the same lattice weights, radial completions and three unit-source anchors are used; probability and optimality are conclusions
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Proposition 4.1, p. 11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=11

import Definitions.Def_TwoItemMenu1393_Main_Distribution
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Proposition 4.1, p. 11.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem proposition_4_1 :
    ∃ c h₀ : ℝ, 0 < c ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      Law (lowerLaw h) ∧ FiniteSupport (lowerLaw h) ∧ Admissible (canonical h) ∧
      revenue (lowerLaw h) (canonical h) = optimum (lowerLaw h) ∧
      ∀ M : Mechanism, Admissible M →
        c*h*(∑ z ∈ fullCenters h, cellSlack h M z) ≤ loss h M ∧
        ∀ i : Fin 3, c*M.u (anchorSource h i) ≤ loss h M ∧
          c*(∑ j : Fin 2, (1 - M.g (anchorTerminal h i) j)) ≤ loss h M := by sorry

end TwoItemMenu1393.Main
