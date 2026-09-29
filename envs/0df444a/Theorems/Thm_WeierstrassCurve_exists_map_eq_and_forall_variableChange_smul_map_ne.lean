-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_map_eq_and_forall_variableChange_smul_map_ne
-- name    : WeierstrassCurve.exists_map_eq_and_forall_variableChange_smul_map_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/702c6f37-eadf-5579-a83f-d838b45e8e41
-- title:
--   A non-trivial first-order deformation of a Weierstrass curve
-- statement:
--   Let $k$ be a field and let $E_0$ be a Weierstrass curve over $k$, i.e. a tuple of coefficients $(a_1,a_2,a_3,a_4,a_6)$ in $k$. The assertion is that there exists a Weierstrass curve $E_1$ over the dual numbers $\mathrm{DualNumber}\,k = k[\varepsilon]/(\varepsilon^2)$ with two properties. First, the coefficientwise image of $E_1$ under the ring homomorphism underlying `TrivSqZeroExt.fstHom k k k`, namely the projection $k[\varepsilon] \to k$ killing $\varepsilon$, is exactly $E_0$; so $E_1$ is a lift of $E_0$ to $k[\varepsilon]$. Second, for every change of variables $C = (u,r,s,t)$ over $k[\varepsilon]$ (with $u$ a unit) whose coefficientwise image under the same projection is the identity change of variables $(1,0,0,0)$, the curve obtained by letting $C$ act on the constant lift $E_0 \otimes_k k[\varepsilon]$, that is on the image of $E_0$ under $\mathrm{algebraMap}\, k\, k[\varepsilon]$, is different from $E_1$. Thus $E_1$ is a first-order deformation of $E_0$ that is not carried to the constant deformation by any change of variables congruent to the identity modulo $\varepsilon$.
--
--   The statement says that the functor of first-order deformations of a Weierstrass curve, taken up to changes of variables trivial modulo $\varepsilon$, is non-trivial: the tangent space to the space of Weierstrass equations modulo coordinate changes is non-zero. It is used in the analysis of the full-level modular curve, being cited by [`ModularCurve.FullLevel.Diamond.exists_forall_eq_map_dualNumber_smul_of_trivial_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.exists_forall_eq_map_dualNumber_smul_of_trivial_rigidDataH1Pow) and [`ModularCurve.FullLevel.exists_forall_eq_map_dualNumber_smul_of_trivial_gamma0Pow`](thm.html#ModularCurve.FullLevel.exists_forall_eq_map_dualNumber_smul_of_trivial_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_map_eq_and_forall_variableChange_smul_map_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.exists_map_eq_and_forall_variableChange_smul_map_ne
    (k : Type*) [Field k] (E₀ : WeierstrassCurve k) :
    ∃ E₁ : WeierstrassCurve (DualNumber k), E₁.map (TrivSqZeroExt.fstHom k k k).toRingHom = E₀ ∧
      ∀ C : WeierstrassCurve.VariableChange (DualNumber k),
        C.map (TrivSqZeroExt.fstHom k k k).toRingHom = 1 →
          C • (E₀.map (algebraMap k (DualNumber k))) ≠ E₁ := by sorry
