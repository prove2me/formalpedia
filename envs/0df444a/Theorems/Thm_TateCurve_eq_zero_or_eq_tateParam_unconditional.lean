-- Prove2me | Theorems.Thm_TateCurve_eq_zero_or_eq_tateParam_unconditional
-- name    : TateCurve.eq_zero_or_eq_tateParam_unconditional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/5c20c338-d54a-5604-b571-e61bb1285aab
-- title:
--   Unconditional p-torsion parametrisation of the Tate curve
-- statement:
--   Let $K$ be a complete, nontrivially normed field with ultrametric distance, of characteristic zero and algebraically closed, and let $q,\zeta,t \in K$ and $p$ a natural number. Assume $q \neq 0$ and $\|q\| < 1$, that $p$ is prime with $p \geq 5$, that $\zeta$ is a primitive $p$-th root of unity, and that $t^p = q$. Let $R$ be a point of the affine Weierstrass curve `curve q`, given by the coefficients $(a_1,a_2,a_3,a_4,a_6) = (1,0,0,a_4(q),a_6(q))$, and suppose $p \cdot R = 0$. Then either $R = 0$, or there are natural numbers $i,j < p$, not both zero, such that the pair $\bigl(\mathrm{pointX}\,q\,(\zeta^i t^j),\ \mathrm{pointY}\,q\,(\zeta^i t^j)\bigr)$ is a nonsingular point of the affine curve and $R$ is the affine point `Point.some` with these coordinates (the conclusion asserts the existence of such a nonsingularity witness). Here, for $u \in K$, $\mathrm{pointX}\,q\,u = \bigl(\sum_{n \in \mathbb{Z}} \mathrm{xfun}(q^n u)\bigr) - 2 s_1(q)$ and $\mathrm{pointY}\,q\,u = \bigl(\sum_{n \in \mathbb{Z}} \mathrm{yfun}(q^n u)\bigr) + s_1(q)$, the sums being the unconditional sums of the corresponding $\mathbb{Z}$-indexed families.
--
--   This is the explicit description of the $p$-torsion of the Tate curve $E_q$ under the Tate uniformisation: $E_q[p] = \{0\} \cup \{(X(\zeta^i t^j), Y(\zeta^i t^j))\}$ with $0 \le i,j < p$ not both zero, as in Silverman's treatment of $q$-expansions for Tate curves. It is the form of the parametrisation carrying no auxiliary hypothesis on $q$, and serves as the input for computations with the Galois action on $E_q[p]$ over complete non-archimedean fields such as $\mathbb{C}_\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateCurve_eq_zero_or_eq_tateParam_unconditional.lean

import Mathlib
import Definitions.Def_TateCurve_XMultAlignment

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve.Affine TateCurve
open scoped NNReal

theorem TateCurve.eq_zero_or_eq_tateParam_unconditional {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [DecidableEq K] [IsAlgClosed K] {q ζ t : K} {p : ℕ} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hp : p.Prime) (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p) (ht : t ^ p = q) (R : (curve q).toAffine.Point) (hR : p • R = 0) : R = 0 ∨ ∃ i j : ℕ, i < p ∧ j < p ∧ ¬(i = 0 ∧ j = 0) ∧ ∃ hns : (curve q).toAffine.Nonsingular (pointX q (ζ ^ i * t ^ j)) (pointY q (ζ ^ i * t ^ j)), R = Point.some (pointX q (ζ ^ i * t ^ j)) (pointY q (ζ ^ i * t ^ j)) hns := by sorry
