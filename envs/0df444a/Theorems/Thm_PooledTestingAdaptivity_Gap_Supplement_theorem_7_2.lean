-- Prove2me | Theorems.Thm_PooledTestingAdaptivity_Gap_Supplement_theorem_7_2
-- name    : PooledTestingAdaptivity.Gap.Supplement.theorem_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:40:57.366269+00:00
-- url     : https://prove2.me/theorems/be9bd1f2-3516-428e-837d-e88bcc193d4f
-- title:
--   Theorem 7.2 — Master upper bounds $W(\pi)\le T_{B\Lambda}$ and $W(\pi)\le Bu^*$
-- statement:
--   Let $J$ be a standard-model instance with pool cap $G$, let $B$ be a test budget, and let $\pi$ be any dynamic policy feasible for $\mathcal F_{B,G}$ (at most $B$ tests, each a nonempty pool of at most $G$ individuals, on every health profile). With the fractional top sum $T_x$ of the values $m_i=u_iq_i$, $u^*=\max_{1\le|t|\le G}q_t\sum_{i\in t}u_i$ and $\Lambda=\max_{1\le|A|\le G}\sum_{i\in A}q_{A\setminus\{i\}}$,
--   $$W(\pi)\le T_{B\Lambda}\qquad\text{and}\qquad W(\pi)\le B\,u^* .$$
--
--   The first bound accounts for each individual being cleared at most once; the second limits the value obtainable per test. Both hold for every feasible policy, normalized or not, and drive the boundary regimes of Theorem 7.3.
--
--   Differences from the source:
--   - encoding: the fractional top sum at the real argument BΛ → topSum of the nonincreasingly sorted list of m_i, zero-extended, at B·Λ; reason: the source's definition of T_x
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Theorem 7.2, printed p. 24, PDF p. 25; definitions §7.1, printed p. 23, PDF p. 24

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_Supplement_Comparison

namespace PooledTestingAdaptivity.Gap.Supplement

/-- Theorem 7.2 (Master upper bounds), printed p. 24, PDF p. 25: every policy feasible for
`F_{B,G}` satisfies `W(π) ≤ T_{BΛ}` and `W(π) ≤ B u*`. -/
theorem theorem_7_2 {n : ℕ} (J : Instance n) (B : ℕ) (π : Policy n)
    (hπ : Feasible (standardFamily J B) π) :
    dynamicWelfare J π ≤ topSum J (B * Lambda J) ∧
      dynamicWelfare J π ≤ B * uStar J := by sorry

end PooledTestingAdaptivity.Gap.Supplement
