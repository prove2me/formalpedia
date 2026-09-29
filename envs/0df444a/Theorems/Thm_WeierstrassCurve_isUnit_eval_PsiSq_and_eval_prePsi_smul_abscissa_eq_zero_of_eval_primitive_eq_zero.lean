-- Prove2me | Theorems.Thm_WeierstrassCurve_isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero
-- name    : WeierstrassCurve.isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/56ea40cb-888a-5a48-b768-2e082bfaf1b4
-- title:
--   Primitive ℓ^k-division points: [ℓ^{k-1}] has ℓ-torsion abscissa
-- statement:
--   Let $T$ be a commutative ring and $W$ a Weierstrass curve over $T$, let $\ell$ be a prime with $\ell\neq 2$, and let $k\geq 1$. Assume that the element $\ell\cdot\Delta(W)$ is a unit of $T$. Let $\Lambda\in T[X]$ be a polynomial realising the factorisation $\mathrm{pre}\Psi_{\ell^k}=\mathrm{pre}\Psi_{\ell^{k-1}}\cdot\Lambda$ of the division polynomials of $W$ (so $\Lambda$ plays the role of the primitive $\ell^k$-division polynomial), and let $x,y\in T$ satisfy the affine Weierstrass equation of $W$, with $\Lambda(x)=0$; nonsingularity of $(x,y)$ is not assumed. Writing $m=\ell^{k-1}$, the conclusion is twofold: first, the value $\Psi^2_m(x)$ is a unit of $T$; second, $\mathrm{pre}\Psi_\ell$ vanishes at the element $\Phi_m(x)\cdot\mathrm{inverse}(\Psi^2_m(x))$, where $\mathrm{inverse}$ denotes the ring inverse, which by the first assertion is the genuine inverse of $\Psi^2_m(x)$. Thus $\Phi_m(x)/\Psi^2_m(x)$, the abscissa of $[m](x,y)$, is a root of the $\ell$-division polynomial $\mathrm{pre}\Psi_\ell$.
--
--   The statement expresses, over an arbitrary base ring in which $\ell$ and the discriminant are invertible, that a point whose abscissa kills the primitive $\ell^k$-division polynomial has $[\ell^{k-1}]$-multiple which is again an affine point (the denominator $\Psi^2_{\ell^{k-1}}$ being invertible) and whose abscissa is an $\ell$-torsion abscissa; the proof uses the separability of the division polynomials under the invertibility hypothesis, the divisibility $\mathrm{pre}\Psi_m \mid \mathrm{pre}\Psi_n$ for $m \mid n$, and the field-theoretic description of vanishing of $\psi_n$ and of the abscissa of $n\cdot P$. It feeds into the construction of $\Gamma_1$-level structures used in [`ModularCurve.IsGamma1Link.of_map_of_surjective_of_ker_pow_eq_bot`](thm.html#ModularCurve.IsGamma1Link.of_map_of_surjective_of_ker_pow_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open Polynomial

theorem WeierstrassCurve.isUnit_eval_PsiSq_and_eval_prePsi_smul_abscissa_eq_zero_of_eval_primitive_eq_zero
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (k : ℕ) (hk : 1 ≤ k)
    (hℓΔ : IsUnit ((ℓ : T) * W.Δ)) {Λ : Polynomial T}
    (hΛ : W.preΨ (ℓ ^ k) = W.preΨ (ℓ ^ (k - 1)) * Λ) (x y : T) (he : W.toAffine.Equation x y) (hx : Λ.eval x = 0) :
    IsUnit ((W.ΨSq (ℓ ^ (k - 1) : ℕ)).eval x) ∧
      (W.preΨ ℓ).eval ((W.Φ (ℓ ^ (k - 1) : ℕ)).eval x * Ring.inverse ((W.ΨSq (ℓ ^ (k - 1) : ℕ)).eval x)) = 0 := by sorry
