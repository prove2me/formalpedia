-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_lemma_3_1
-- name    : TwoItemMenu1393.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:24:50.716821+00:00
-- url     : https://prove2.me/theorems/51d08f02-7a92-4db3-8953-788bd61f0375
-- title:
--   Lemma 3.1 — Supporting-plane sub-menu approximation
-- statement:
--   Let $(u,g)$ be any admissible mechanism, and let $R,t>0$. There exists a finite set $J\subset[0,R]^2$ such that
--   $$|J|\le\left\lceil\frac{R+1}{t}\right\rceil^2,\qquad u(v)-t^2/2\le u_J(v)\le u(v)\quad(v\in[0,R]^2).$$
--   Here $u_J$ is the envelope of the tangent entries $(g(s),g(s)\cdot s-u(s))$ at $s\in J$, together with null. Representatives may lie outside the unit type square when $R>1$. The statement preserves the factor $1/2$ and the square of the ceiling. It provides the utility approximation used in the universal revenue bound.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
--   - encoding: integer ceiling and finite representative sets → natural ceiling and Finset representatives; reason: the ceiling argument is positive, so the ceilings agree and all finite sets are represented
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Lemma 3.1, p. 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=6

import Definitions.Def_TwoItemMenu1393_Main_Model
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Lemma 3.1, p. 6.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem lemma_3_1 (M : Mechanism) (hM : Admissible M)
    (R t : ℝ) (hR : 0 < R) (ht : 0 < t) :
    ∃ J : Finset Vec, (∀ s ∈ J, s ∈ square R) ∧
      J.card ≤ (⌈(R+1)/t⌉₊)^2 ∧
      ∀ v ∈ square R, M.u v - t^2/2 ≤ subUtility M J v ∧ subUtility M J v ≤ M.u v := by sorry

end TwoItemMenu1393.Main
