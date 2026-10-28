-- Prove2me | Theorems.Thm_QAOAE3Lin2_Typical_eq_48
-- name    : QAOAE3Lin2.Typical.eq_48
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:50.878324+00:00
-- url     : https://prove2.me/theorems/e8d0529a-23a2-410b-8782-e8258186c8ab
-- title:
--   Section III, (48), p. 10 — for every fixed z, E_d[cos(γc_r)] = (cos γ)^{D_r}, D_r the number of terms of c_r
-- statement:
--   Fix any triples, an equation $i$, a role $\rho\in\{1,2,3\}$, an angle $\gamma\in\mathbb R$ and a bit string $z$. Let $c_\rho(z)=\sum d_{\rho ab}z_az_b$ be the polynomial (21), with $D_\rho$ terms. When the right-hand sides are drawn uniformly from $\{0,1\}^m$,
--   $$\mathbb E_d\big[\cos(\gamma c_\rho(z))\big]=\prod_{a<b}\cos\gamma=(\cos\gamma)^{D_\rho},$$
--   the product running over the pairs with $d_{\rho ab}\neq0$. In particular the average does not depend on $z$.
--
--   This is the average-over-signs computation that turns (47) into the closed form (49).
--
--   **Formalization Note** $\mathbb E_d$ is the uniform average over all $2^m$ right-hand-side vectors. No hypothesis on the triples is needed: each term of $c_\rho$ carries its own independent sign.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm Applied to a Bounded Occurrence Constraint Problem, arXiv:1412.6062v2, p. 10, Section III, (48)

import Mathlib
import Definitions.Def_QAOAE3Lin2_Typical_Setting

namespace QAOAE3Lin2.Typical

/-- (48), p. 10: for every fixed bit string `x`, the average over the instances of `cos(γ c_r)` is
`(cos γ)^{D_r}`, where `D_r` is the number of terms of `c_r`; it does not depend on `x`. -/
theorem eq_48 {n m : ℕ} (tri : Fin m → Fin n × Fin n × Fin n) (i : Fin m) (r : Fin 3) (γ : ℝ)
    (x : QAlgorithms.Qubits n) :
    avgD (fun rhs => Real.cos (γ * QAOAE3Lin2.General.cPoly tri rhs i r x)) = Real.cos γ ^ QAOAE3Lin2.General.termCount tri i r := by sorry

end QAOAE3Lin2.Typical
