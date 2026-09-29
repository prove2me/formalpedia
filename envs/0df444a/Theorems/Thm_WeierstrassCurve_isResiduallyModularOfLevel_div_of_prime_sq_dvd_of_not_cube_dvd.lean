-- Prove2me | Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_prime_sq_dvd_of_not_cube_dvd
-- name    : WeierstrassCurve.isResiduallyModularOfLevel_div_of_prime_sq_dvd_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/32bd0700-a245-5205-9c85-1f0a592fac9c
-- title:
--   Level lowering at q when q² ∣ M, q³ ∤ M
-- statement:
--   Let $p$ be a prime with $p \neq 2$ and let $W$ be a Weierstrass equation over $\mathbb{Z}$ with $\Delta(W) \neq 0$ which is a semistable model, i.e. for every prime $\ell$ dividing $\Delta(W)$ one has $\ell \nmid c_4(W)$. Assume: the $p$-torsion subgroup of the points of $W$ base-changed to an algebraic closure of $\mathbb{Q}$ has exactly $p^2$ elements; the action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on that $p$-torsion, viewed as a homomorphism into the $\mathbb{Z}/p$-linear endomorphisms, factors through a finite level, i.e. there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every automorphism fixing $L$ pointwise acts as the identity; and this $p$-torsion module is irreducible, meaning it is nontrivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $\bot$ and $\top$. Let $M$ be a natural number and $q \neq p$ a prime with $q^2 \mid M$ and $q^3 \nmid M$. Suppose $W$ is residually modular of level $M$: there are a weight-$2$ cusp form $f$ on $\Gamma_0(M)$ and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ with $p \in \mathfrak{m}$, such that $f$ is a normalised eigenform (first $q$-expansion coefficient $1$, multiplicativity at coprime indices, and the usual Hecke recursions at prime powers, in the two forms according to whether the prime divides $M$), and for every prime $\ell$ with $\ell \nmid \Delta(W)$, $\ell \nmid M$, $\ell \neq p$ there is an algebraic integer $a$ with $a$ equal to the $\ell$-th $q$-expansion coefficient of $f$ and $a - a_\ell(W) \in \mathfrak{m}$, where $a_\ell(W)$ is the trace of Frobenius of the reduction of $W$ modulo $\ell$. The conclusion is that $W$ is residually modular of level $M/q$ (natural-number division).
--
--   This is the level-lowering step at a prime $q$ exactly dividing $M$ to the second power, in the form used to strip the level of the mod-$p$ representation of a semistable elliptic curve down to its minimal level. It is applied in the passage from a given level to the minimal level, both in the case of an exact square and in the case where $q^2 \nmid M$ is treated separately.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_prime_sq_dvd_of_not_cube_dvd.lean

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.isResiduallyModularOfLevel_div_of_prime_sq_dvd_of_not_cube_dvd
    (p : ℕ) [Fact p.Prime] (_hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (_hΔ : W.Δ ≠ 0)
    (_hW : W.IsSemistableModel)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (_hirr : W.ModRepIsIrreducible p) (M q : ℕ) (hq : q.Prime) (hqp : q ≠ p)
    (hq2 : q ^ 2 ∣ M)

    (hq3 : ¬ q ^ 3 ∣ M)
    (hres : W.IsResiduallyModularOfLevel p M) :
    W.IsResiduallyModularOfLevel p (M / q) := by sorry
