-- Prove2me | Theorems.Thm_PolyhedralSOC_LowerBound_slice_convex_hull
-- name    : PolyhedralSOC.LowerBound.slice_convex_hull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:48:52.91221+00:00
-- url     : https://prove2.me/theorems/ad39e7cf-0792-4508-bbb2-4c2392c11f4f
-- title:
--   Proposition 3.1, proof — $G$ is the convex hull of at most $2^q$ points
-- statement:
--   Let $\varepsilon>0$ and let $\Pi:\mathbb R^k\times\mathbb R\times\mathbb R^p\to\mathbb R^q$ be a polyhedral $\varepsilon$-approximation of $L^k$ whose cone $K=\{(y,t,u)\mid\Pi(y,t,u)\ge0\}$ contains no line. Let $G=\{y\mid \Pi(y,1,u)\ge 0\ \text{for some } u\}$. Then there is a finite set $\{y_1,\dots,y_N\}\subseteq\mathbb R^k$ with $N\le 2^q$ such that
--   $$G=\operatorname{conv}\{y_1,\dots,y_N\}.$$
--
--   In the paper: the projection $\widehat L^k$ of $K$ onto the $(y,t)$-space is the conic hull of the $N\le 2^q$ projected extreme rays $R_1,\dots,R_N$ of $K$, each meeting the hyperplane $H=\{t=1\}$, and $y_i$ is the $y$-component of $R_i\cap H$. This turns the number of inequalities $q$ into a bound on the number of vertices of $G$.
-- source:
--   Ben-Tal & Nemirovski, On Polyhedral Approximations of the Second-Order Cone, Math. Oper. Res. 26(2):193–205 (2001), p. 202, Proposition 3.1, proof ("G is the convex hull of N points y_1, …, y_N")

import Mathlib
import Definitions.Def_PolyhedralSOC_Shared_LorentzCone
import Definitions.Def_PolyhedralSOC_Shared_IsPolyhedralApprox
import Definitions.Def_PolyhedralSOC_LowerBound_ProofObjects

namespace PolyhedralSOC.LowerBound

/-- Ben-Tal & Nemirovski, *On Polyhedral Approximations of the Second-Order Cone*,
Math. Oper. Res. 26(2):193–205 (2001), Proposition 3.1, proof, p. 202 (PDF p. 10):
once the cone `K = {Π ≥ 0}` contains no line, the projection `L̂^k` of `K` onto the
`(y, t)`-space is the conic hull of `N ≤ 2^q` rays, each meeting `H = {t = 1}`, and
"G is the convex hull of N points y_1, …, y_N — the y components of the intersections
R_i ∩ H". Here `G = {y | Π(y, 1, u) ≥ 0 for some u}` and the bound `N ≤ 2^q` is the one
established earlier in the same proof. -/
theorem slice_convex_hull {k p q : ℕ} {ε : ℝ} (hε : 0 < ε)
    (P : (Fin k → ℝ) × ℝ × (Fin p → ℝ) →ₗ[ℝ] (Fin q → ℝ))
    (hP : Shared.IsPolyhedralApprox k p q ε P) (hK : IsLineFree P) :
    ∃ S : Finset (Fin k → ℝ), S.card ≤ 2 ^ q ∧
      convexHull ℝ (S : Set (Fin k → ℝ)) = sliceG P := by sorry

end PolyhedralSOC.LowerBound
