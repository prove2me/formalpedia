-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_theorem_1_2
-- name    : TwoItemMenu1393.Main.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:24:44.293337+00:00
-- url     : https://prove2.me/theorems/2bc39eda-4068-4571-955c-13a5199191d1
-- title:
--   Theorem 1.2 — Finite-support lower bound and tight worst-case rate
-- statement:
--   There are positive constants $c,C,\varepsilon_0$ such that for every $0<\varepsilon<\varepsilon_0$ there is a finitely supported Borel probability law $F_\varepsilon$ on the continuous square $[0,1]^2$ with
--   $$M_{F_\varepsilon}(\varepsilon)\ge c\varepsilon^{-2},\qquad c\varepsilon^{-2}\le M(\varepsilon)\le C\varepsilon^{-2}.$$
--   Thus $M(\varepsilon)=\Theta(\varepsilon^{-2})$ as $\varepsilon\to0^+$. The constants precede the error and law quantifiers; the witness law may depend on the error. Competitors in each complexity infimum include every admissible mechanism, with arbitrary Borel subgradient selections and no support, independence or density restriction. The witness law alone has finite support. This is the whole lower-bound theorem, including its two-sided consequent.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: Borel probability laws on the type square → ambient Borel measures with total mass one and zero mass off the square; reason: pushforward along the square inclusion gives precisely the same laws and integrals
--   - encoding: nonnegative integer menu sizes with possible infinity → infima and suprema of natural numbers embedded in ℝ≥0∞; reason: empty feasible sets retain infinity and zero-size menus remain allowed
--   - encoding: the lower bound and its Θ consequent → positive constants c,C,ε₀ and both inequalities on the same punctured right neighborhood; reason: shrinking the threshold combines the source lower bound and the universal upper bound without changing either assertion
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Theorem 1.2, p. 4. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=4

import Definitions.Def_TwoItemMenu1393_Main_Model
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Theorem 1.2, p. 4.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem theorem_1_2 :
    ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (∃ F : Measure Vec, Law F ∧ FiniteSupport F ∧
          ENNReal.ofReal (c/ε^2) ≤ complexity F ε) ∧
        ENNReal.ofReal (c/ε^2) ≤ worstComplexity ε ∧
        worstComplexity ε ≤ ENNReal.ofReal (C/ε^2) := by sorry

end TwoItemMenu1393.Main
