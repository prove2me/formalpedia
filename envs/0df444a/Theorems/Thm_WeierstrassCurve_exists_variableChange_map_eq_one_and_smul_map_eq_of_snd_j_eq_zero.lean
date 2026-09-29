-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_map_eq_one_and_smul_map_eq_of_snd_j_eq_zero
-- name    : WeierstrassCurve.exists_variableChange_map_eq_one_and_smul_map_eq_of_snd_j_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/b148bb87-dbc3-528a-9193-53082b7ab041
-- title:
--   Constant j forces infinitesimal triviality of Weierstrass deformations
-- statement:
--   Let $k$ be a field in which $2 \neq 0$ and $3 \neq 0$, and let $k[\varepsilon] = \mathrm{DualNumber}\ k$ be the dual numbers over $k$. Let $E_0$ be a Weierstrass curve over $k$ that is elliptic (its discriminant is a unit), with $j$-invariant satisfying $j(E_0) \neq 0$ and $j(E_0) \neq 1728$. Let $E$ be a Weierstrass curve over $k[\varepsilon]$, again elliptic, whose image under the coefficientwise map induced by the first-component ring homomorphism $k[\varepsilon] \to k$ (which sends $\varepsilon$ to $0$) equals $E_0$; thus $E$ is a first-order deformation of $E_0$. Assume the $\varepsilon$-component of the $j$-invariant $j(E) \in k[\varepsilon]$ vanishes, i.e. $j(E)$ lies in $k$. Then there exists a Weierstrass variable change $C = (u, r, s, t)$ over $k[\varepsilon]$ whose reduction along $k[\varepsilon] \to k$ is the identity variable change $1$, such that applying $C$ to the constant deformation $E_0 \otimes_k k[\varepsilon]$ (the base change of $E_0$ along the structure map $k \to k[\varepsilon]$) yields exactly $E$.
--
--   This is the infinitesimal rigidity statement underlying the fact that, away from the elliptic points $j = 0, 1728$, the $j$-line is étale over the moduli problem of Weierstrass curves: a first-order Weierstrass deformation with constant $j$-invariant is isomorphic to the constant one by an infinitesimally trivial change of variables. It is used in the analysis of tangent vectors to modular curves at points of full level and $\Gamma_0$-type level structures, where it forces the $\varepsilon$-part of the $j$-invariant of a tangent vector to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_map_eq_one_and_smul_map_eq_of_snd_j_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_variableChange_map_eq_one_and_smul_map_eq_of_snd_j_eq_zero
    (k : Type) [Field k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (E₀ : WeierstrassCurve k) [E₀.IsElliptic] (hj0 : E₀.j ≠ 0) (hj1728 : E₀.j ≠ 1728)
    (E : WeierstrassCurve (DualNumber k)) [E.IsElliptic]
    (hE : E.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀)
    (hj : TrivSqZeroExt.snd E.j = 0) :
    ∃ C : WeierstrassCurve.VariableChange (DualNumber k),
      C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 ∧
      C • (E₀.map (algebraMap k (DualNumber k))) = E := by sorry
