-- Prove2me | Theorems.Thm_PConeEB_theorem_4_2
-- name    : PConeEB.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:34:24.359284+00:00
-- url     : https://prove2.me/theorems/d094b4db-0aed-4073-90bd-67ddd2008a26
-- title:
--   Theorem 4.2 — (G1) is satisfied for $p$-cones
-- statement:
--   Let $n\ge2$, $p,q\in(1,\infty)$ with $\frac1p+\frac1q=1$, $z\in\partial\mathcal K_q^{n+1}\setminus\{0\}$, and $\alpha_z$ as in (4.6). Then the function $\mathfrak g=|\cdot|^{\alpha_z}$ satisfies the asymptotic optimality criterion (G1) for $\mathcal K_p^{n+1}$ and $z$.
--
--   This is the tightness half of the main theorem at the level of a single face.
--
--   Differences from the source:
--   - encoding: (G1): w : (0, 1] → {z}^⊥ ∩ span K \ F continuous, L_g = limsup < ∞ → SatisfiesG1 with a total w, the conditions on Set.Ioc 0 1, and an ENNReal limsup equal to ENNReal.ofReal Lg with 0 ≤ Lg; reason: Lean conventions; same instances, and an ENNReal limsup has no boundedness side condition
--   - encoding: ℝ^{n+1}, x₀, x̄, ‖x̄‖_p, ∂ → RR n = EuclideanSpace ℝ (Fin (n + 1)), x 0, x i.succ for i : Fin n, pNorm with real rpow, frontier; reason: Lean conventions; same instances
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Theorem 4.2, p.24

import Mathlib
import Definitions.Def_PConeEB_pCone
import Definitions.Def_PConeEB_alphaZ
import Definitions.Def_PConeEB_SatisfiesG1

namespace PConeEB

/-- Theorem 4.2 (the optimality criterion (G1) is satisfied for `p`-cones). For `n ≥ 2`,
`1/p + 1/q = 1`, `z ∈ ∂K_q^{n+1} \ {0}`, the function `g = |·|^{α_z}` satisfies the asymptotic
optimality criterion (G1) for `K_p^{n+1}` and `z`.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Theorem 4.2, p.24. -/
theorem theorem_4_2 {n : ℕ} (hn : 2 ≤ n) {p q : ℝ} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1)
    {z : RR n} (hz : z ∈ frontier (pCone n q)) (hz0 : z ≠ 0) :
    ∃ (v : RR n) (w : ℝ → RR n) (Lg : ℝ),
      SatisfiesG1 (pCone n p) z (fun t => |t| ^ alphaZ p z) v w Lg := by sorry

end PConeEB
