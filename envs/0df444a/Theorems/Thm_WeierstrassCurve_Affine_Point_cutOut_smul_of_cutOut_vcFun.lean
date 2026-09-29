-- Prove2me | Theorems.Thm_WeierstrassCurve_Affine_Point_cutOut_smul_of_cutOut_vcFun
-- name    : WeierstrassCurve.Affine.Point.cutOut_smul_of_cutOut_vcFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.868498+00:00
-- url     : https://prove2.me/theorems/ecc38fd9-e938-500c-80d1-1f8e83c28152
-- title:
--   Transport of the cut-out condition under a variable change
-- statement:
--   Let $K$ be a field, $W$ a Weierstrass curve over $K$, $C$ a Weierstrass variable change over $K$ (with parameters $u \in K^\times$, $r$, $s$, $t$), and $M'$ a nonzero natural number. Let $h$ assign to each prime factor $p$ of $M'$ a polynomial $h_p \in K[X]$, assume each $h_p$ is monic and that $\deg h_p \le d_p := \mathrm{gamma0PowDeg}(p, v_p(M'))$, where $\mathrm{gamma0PowDeg}(p,k)$ is $1$ if $p^k = 2$ and $\varphi(p^k)/2$ otherwise, and $v_p(M')$ is the exponent of $p$ in $M'$. Let $g'$ be a point of the affine curve $C \bullet W$, and write $g = \mathrm{vcFun}\,C\,W\,g'$ for its image in $W(K)$ under the map sending $0$ to $0$ and an affine point $(x',y')$ to $(\mathrm{vcX}\,C\,x', \mathrm{vcY}\,C\,x'\,y')$, the first coordinate being $u^2x' + r$. Assume that $g$ has additive order $M'$ and that, for every prime factor $p$ of $M'$, every $n \in \mathbb{N}$ and every nonsingular affine point $(x_1,y_1)$ of $W$ with $n \cdot g = (x_1,y_1)$ and $\mathrm{addOrderOf}(n \cdot g) = p^{v_p(M')}$, one has $h_p(x_1) = 0$. The conclusion is that $g'$ itself has additive order $M'$ and that, for every such $p$, every $n \in \mathbb{N}$ and every nonsingular affine point $(x_1,y_1)$ of $C \bullet W$ with $n \cdot g' = (x_1,y_1)$ and $\mathrm{addOrderOf}(n \cdot g') = p^{v_p(M')}$, the abscissa $x_1$ is a root of $\mathrm{kernelVariableChangeDeg}\,C\,d_p\,h_p = (u^{-1})^{2d_p} \cdot h_p(u^2X + r)$.
--
--   This is the compatibility of a "cut-out" condition on a point of prescribed order — that the abscissae of the relevant multiples be roots of a prescribed monic polynomial of controlled degree — with a change of Weierstrass coordinates, the polynomial being replaced by its normalised pullback along $x \mapsto u^2x + r$. It is used in the construction of moduli points for the level structures, where two presentations of the same curve differing by a variable change must be shown to yield the same datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Affine_Point_cutOut_smul_of_cutOut_vcFun.lean

import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_VariableChangePointEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem WeierstrassCurve.Affine.Point.cutOut_smul_of_cutOut_vcFun
    (K : Type) [Field K] [DecidableEq K] (W : WeierstrassCurve K) (C : WeierstrassCurve.VariableChange K)
    (M' : ℕ) [NeZero M'] (h : ↥M'.primeFactors → Polynomial K)
    (hmonic : ∀ p, (h p).Monic) (hdeg : ∀ p : ↥M'.primeFactors, (h p).natDegree ≤ ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ)))
    (g' : (C • W).toAffine.Point)
    (hg : (addOrderOf (WeierstrassCurve.Affine.Point.vcFun C W g') = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : K) (h₁ : (W).toAffine.Nonsingular x₁ y₁),
          n • (WeierstrassCurve.Affine.Point.vcFun C W g') = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • (WeierstrassCurve.Affine.Point.vcFun C W g')) = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (h p).IsRoot x₁)) :
    (addOrderOf g' = M' ∧
        ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : K) (h₁ : (C • W).toAffine.Nonsingular x₁ y₁),
          n • g' = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g') = (p : ℕ) ^ M'.factorization (p : ℕ) →
          (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (p : ℕ) (M'.factorization (p : ℕ))) (h p)).IsRoot x₁) := by sorry
