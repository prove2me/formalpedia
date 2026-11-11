-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_theorem_1_1
-- name    : TwoItemMenu1393.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:24:42.432507+00:00
-- url     : https://prove2.me/theorems/1bf9042a-6ca5-4ae2-877c-612b5e418d21
-- title:
--   Theorem 1.1 — Universal upper bound with ceiling constant four
-- statement:
--   For every Borel probability law $F$ on $[0,1]^2$ and every $0<\varepsilon\le1$, there exists an admissible mechanism with at most $\lceil4/\varepsilon\rceil^2$ nonnull entries and revenue at least $\mathrm{OPT}(F)-\varepsilon$. In particular,
--   $$M(\varepsilon)\le\lceil4/\varepsilon\rceil^2=O(\varepsilon^{-2})\quad(\varepsilon\to0^+).$$
--   The big-O assertion uses positive constants uniform in $F$ and $\varepsilon$ on a punctured right neighborhood of zero. This includes correlated, atomic, singular and continuous laws and keeps the exact ceiling constant four over the entire stated error domain. It is the universal branch of the tight worst-case rate.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: Borel probability laws on the type square → ambient Borel measures with total mass one and zero mass off the square; reason: pushforward along the square inclusion gives precisely the same laws and integrals
--   - encoding: nonnegative integer menu sizes with possible infinity → infima and suprema of natural numbers embedded in ℝ≥0∞; reason: empty feasible sets retain infinity and zero-size menus remain allowed
--   - encoding: big-O as ε tends to zero from the right → positive uniform constants C,ε₀ with M(ε)≤C/ε² whenever 0<ε<ε₀; reason: this is exactly the one-sided asymptotic bound
--   - encoding: integer ceiling of 4/ε → natural ceiling of 4/ε; reason: the argument is positive on the entire stated domain, so the ceilings agree
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Theorem 1.1, p. 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=3

import Definitions.Def_TwoItemMenu1393_Main_Model
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Theorem 1.1, p. 3.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem theorem_1_1 :
    (∀ (F : Measure Vec) (ε : ℝ), Law F → 0 < ε → ε ≤ 1 →
      ∃ M : Mechanism, Admissible M ∧ MenuSizeAtMost M (⌈4/ε⌉₊^2) ∧
        optimum F - ε ≤ revenue F M) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → worstComplexity ε ≤ (⌈4/ε⌉₊^2 : ℕ)) ∧
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      worstComplexity ε ≤ ENNReal.ofReal (C/ε^2) := by sorry

end TwoItemMenu1393.Main
