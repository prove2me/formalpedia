-- Prove2me | Theorems.Thm_WeierstrassCurve_map_frobenius_dualNumber_eq_map_map_map
-- name    : WeierstrassCurve.map_frobenius_dualNumber_eq_map_map_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/9cc8bcec-de23-52da-93ef-88649d63fdf4
-- title:
--   Frobenius twist over the dual numbers is constant
-- statement:
--   Let $q$ be a prime number and $k$ a field of characteristic $q$, and let $\mathrm{DualNumber}\,k = k[\varepsilon]$, $\varepsilon^2 = 0$, be assumed to have characteristic $q$ as well (this is assumed, not derived). Let $W$ be a Weierstrass curve over $k[\varepsilon]$, i.e. a tuple of coefficients $a_1, a_2, a_3, a_4, a_6 \in k[\varepsilon]$. The assertion is an equality of Weierstrass curves over $k[\varepsilon]$, obtained by applying ring homomorphisms coefficientwise: the base change of $W$ along the $q$-power Frobenius endomorphism $x \mapsto x^q$ of $k[\varepsilon]$ coincides with the curve obtained from $W$ by first pushing forward along the ring homomorphism underlying the first projection $k[\varepsilon] \to k$ (the algebra map `TrivSqZeroExt.fstHom k k k`), then along the $q$-power Frobenius of $k$, and finally along the structure map $k \to k[\varepsilon]$. In other words, the Frobenius twist of a Weierstrass curve over the dual numbers is the constant extension to $k[\varepsilon]$ of the Frobenius twist of its reduction over $k$.
--
--   This records the fact that a first-order deformation of a Weierstrass curve in characteristic $q$ becomes constant after the Frobenius twist, since the nilpotent part is killed by the $q$-th power map. It is used in the construction of models over the dual numbers in `WeierstrassCurve.DrinfeldGlobal.exists_iso_projModelCR_map_map_map_of_frobenius_of_comp_schemeNsmul_eq_one_of_nsmul_eq_one`, where a twisted curve has to be identified with a base change from $k$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_map_frobenius_dualNumber_eq_map_map_map.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.map_frobenius_dualNumber_eq_map_map_map
    (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] [CharP (DualNumber k) q]
    (W : WeierstrassCurve (DualNumber k)) :
    W.map (frobenius (DualNumber k) q) =
      ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (frobenius k q)).map (algebraMap k (DualNumber k)) := by sorry
