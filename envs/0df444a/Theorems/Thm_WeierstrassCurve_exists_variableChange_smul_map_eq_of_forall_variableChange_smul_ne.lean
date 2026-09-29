-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne
-- name    : WeierstrassCurve.exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/de385073-52a3-5aee-b31e-3e00b150fceb
-- title:
--   First-order Weierstrass deformations form a line
-- statement:
--   Let $k$ be a field and let $E_0$ be a Weierstrass curve over $k$ which is elliptic, i.e. whose discriminant is a unit. Write $k[\varepsilon]$ for the dual numbers `DualNumber k` over $k$, with the reduction ring homomorphism attached to `TrivSqZeroExt.fstHom k k k`, which sends $a + b\varepsilon$ to $a$. Let $E_1$ be a Weierstrass curve over $k[\varepsilon]$ whose coefficientwise image under this reduction is $E_0$, and assume that $E_1$ is not obtained from the base change of $E_0$ along $k \to k[\varepsilon]$ by any admissible change of Weierstrass variables $C = (u, r, s, t)$ over $k[\varepsilon]$ whose reduction is the identity change of variables, that is, with $u \equiv 1$ and $r \equiv s \equiv t \equiv 0 \pmod{\varepsilon}$. Then for every Weierstrass curve $E$ over $k[\varepsilon]$ reducing to $E_0$ there exist a scalar $c \in k$ and an admissible change of variables $C$ over $k[\varepsilon]$ reducing to the identity such that $C$ applied to the image of $E_1$ under the ring endomorphism of $k[\varepsilon]$ given by `TrivSqZeroExt.map (c • LinearMap.id)`, namely $a + b\varepsilon \mapsto a + cb\varepsilon$, equals $E$.
--
--   This is the computation of the tangent space to the moduli of elliptic curves at $E_0$: first-order Weierstrass deformations of an elliptic curve, taken modulo changes of variables infinitesimally close to the identity, are exhausted by the rescalings of a single non-trivial deformation, so that space is at most one-dimensional over $k$, in every characteristic. It is used in the construction of infinitesimal data on modular curves, being cited by [`ModularCurve.FullLevel.Diamond.exists_forall_eq_map_dualNumber_smul_of_trivial_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.exists_forall_eq_map_dualNumber_smul_of_trivial_rigidDataH1Pow) and [`ModularCurve.FullLevel.exists_forall_eq_map_dualNumber_smul_of_trivial_gamma0Pow`](thm.html#ModularCurve.FullLevel.exists_forall_eq_map_dualNumber_smul_of_trivial_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_variableChange_smul_map_eq_of_forall_variableChange_smul_ne
    (k : Type) [Field k] (E₀ : WeierstrassCurve k) [E₀.IsElliptic]
    (E₁ : WeierstrassCurve (DualNumber k)) (hE₁ : E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀)
    (hE₁' : ∀ C : WeierstrassCurve.VariableChange (DualNumber k),
      C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 → C • (E₀.map (algebraMap k (DualNumber k))) ≠ E₁)
    (E : WeierstrassCurve (DualNumber k)) (hE : E.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀) :
    ∃ (c : k) (C : WeierstrassCurve.VariableChange (DualNumber k)),
      C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 ∧
      C • (E₁.map (TrivSqZeroExt.map (c • LinearMap.id : k →ₗ[k] k)).toRingHom) = E := by sorry
