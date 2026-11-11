-- Prove2me | Theorems.Thm_TwoItemMenu1393_Main_lemma_B_2
-- name    : TwoItemMenu1393.Main.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:24:35.653792+00:00
-- url     : https://prove2.me/theorems/2aabe302-1d85-4dc5-8c2a-2aaa538a719f
-- title:
--   Lemma B.2 — Normalized utility representation
-- statement:
--   Let $(q,p)$ be a Borel direct IC/IR mechanism on $[0,1]^2$, with truthful utility $u(v)=q(v)\cdot v-p(v)$ and $u(0)=0$. Its extension
--   $$\bar u(v)=\sup\bigl(\{0\}\cup\{q(w)\cdot v-p(w):w\in[0,1]^2\}\bigr)$$
--   belongs to $\mathcal U$, agrees with $u$ on the square, satisfies $q(v)\in\partial\bar u(v)$ and preserves every payment there. Conversely, every $u\in\mathcal U$ with a Borel subgradient selection gives a direct IC/IR mechanism on the square with utility $u$ and with $p(v)\ge0$ on all of $\mathbb R^2$. This supplies both directions of the utility representation used throughout the mission.
--
--   Differences from the source:
--   - encoding: two real coordinates → EuclideanSpace ℝ (Fin 2); reason: the coordinate isometry preserves dot products, Borel sets, Euclidean norms and all instances
-- source:
--   Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393 (October 2026), Lemma B.2, p. 17. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1393.pdf#page=17

import Definitions.Def_TwoItemMenu1393_Main_Model
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace TwoItemMenu1393.Main

/-- Hau Chan, Mingyu Guo, Nguyen Thach, STOC 2027 submission #1393
(October 2026), Lemma B.2, p. 17.
Pinned PDF sha256: 9b1049b1045e4c9f8fe08a35eb33749c850548cb87464793e3f41f1b615fbb3e. -/
theorem lemma_B_2 :
    (∀ D : DirectMechanism, DirectAdmissible D →
      (∀ v : TypeSquare, (v : Vec) = 0 → directUtility D v = 0) →
      Utility (directEnvelope D) ∧
        ∀ v : TypeSquare, directEnvelope D v = directUtility D v ∧
          Subgradient (directEnvelope D) v (D.q v) ∧
          D.p v = dot (D.q v) v - directEnvelope D v) ∧
    (∀ M : Mechanism, Admissible M →
      DirectAdmissible (directRestriction M) ∧
      (∀ v : TypeSquare, directUtility (directRestriction M) v = M.u v) ∧
      ∀ v : Vec, 0 ≤ payment M v) := by sorry

end TwoItemMenu1393.Main
