-- Prove2me | Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf
-- name    : WeierstrassCurve.isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/30f82250-c631-5359-bd25-f387df2a030e
-- title:
--   Level lowering at a prime q≡ 1mod p dividing M exactly
-- statement:
--   Let $p$ be a prime (registered as such by a `Fact` instance) with $p\neq 2$, and let $W$ be a Weierstrass equation over $\mathbb{Z}$ with $\Delta_W\neq 0$ which is a semistable model in the project's sense (for every prime $\ell$ with $\ell\mid\Delta_W$ one has $\ell\nmid c_4(W)$). Write $W_{\mathbb{Q}}$ for the base change of $W$ along $\mathbb{Z}\to\mathbb{Q}$. Assume: the $p$-torsion subgroup of the group of points of $W_{\mathbb{Q}}$ over $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ` has exactly $p^2$ elements; the monoid homomorphism sending $\sigma\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to its induced $\mathbb{Z}/p$-endomorphism of that $p$-torsion module factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite over $\mathbb{Q}$, such that every $\sigma$ fixing $L$ pointwise acts as the identity; and `W.ModRepIsIrreducible p` holds, i.e. the $p$-torsion module is nontrivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $\bot$ and $\top$. Let $M,q$ be naturals with $q$ prime, $q\neq p$, $q\mid M$, $q^2\nmid M$ and $M$ squarefree. Assume the residual representation $\bar\rho$ attached to these data (the two-dimensional $\mathbb{Z}/p$-representation on the $p$-torsion, packaged by `residualGaloisRepOf`) is unramified at $q$ in the project's sense: for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, every element of the inertia subgroup of $A$ over $\mathbb{Q}$ acts trivially. Assume further $q\equiv 1\pmod p$, i.e. the image of $q$ in $\mathbb{Z}/p$ is $1$. Finally assume `W.IsResiduallyModularOfLevel p M`: there are a normalized eigenform $f$ of weight $2$ on $\Gamma_0(M)$ (normalized in the sense of the project's structure on $q$-expansion coefficients: first coefficient $1$, multiplicativity at coprime indices, and the two recursions at prime powers) and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, such that for every prime $\ell$ with $\ell\nmid\Delta_W$, $\ell\nmid M$ and $\ell\neq p$ there is an algebraic integer $a$ equal to the $\ell$-th $q$-expansion coefficient of $f$ with $a\equiv a_\ell(W)\pmod{\mathfrak{m}}$, where $a_\ell(W)$ is the trace of Frobenius of the reduction of $W$ modulo $\ell$. The conclusion is the same assertion at level $M/q$: `W.IsResiduallyModularOfLevel p (M / q)`.
--
--   This is the case $q\equiv 1\pmod p$ of Ribet's theorem on lowering the level at a prime exactly dividing it, stated here not as a statement about modular representations but concretely: the existence of a weight-two normalized eigenform at level $M$ whose Hecke eigenvalues are congruent, modulo a maximal ideal above $p$ of the ring of algebraic integers, to the Frobenius traces of $W$, implies the existence of such an eigenform at level $M/q$. No newness or minimality of the resulting form is asserted, and the semistability hypothesis on $W$ is carried in the hypothesis list without entering the derivation. It is the complement, at primes $q\equiv 1\pmod p$, of the case handled by Mazur's principle, and the two cases are combined in [`WeierstrassCurve.isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf), which removes the congruence condition on $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf.lean

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.isResiduallyModularOfLevel_div_of_cast_eq_one_of_isUnramifiedAt_sqf
    (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (_hΔ : W.Δ ≠ 0)
    (_hW : W.IsSemistableModel)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (_hirr : W.ModRepIsIrreducible p) (M q : ℕ) (hq : q.Prime) (hqp : q ≠ p)
    (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M) (hM : Squarefree M)
    (hunr : ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).IsUnramifiedAt q)
    (hq1 : ((q : ℕ) : ZMod p) = 1)
    (hres : W.IsResiduallyModularOfLevel p M) :
    W.IsResiduallyModularOfLevel p (M / q) := by sorry
