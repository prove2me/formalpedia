-- Prove2me | Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf
-- name    : WeierstrassCurve.isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/afb0782e-4893-5c25-9458-047eec59b3a8
-- title:
--   Level lowering at an unramified prime exactly dividing the level
-- statement:
--   Fix a natural number $p$ which is prime (as a `Fact` instance) and assume $p \neq 2$. Let $W$ be a Weierstrass equation over $\mathbb{Z}$ with $\Delta_W \neq 0$ which satisfies the project's semistability predicate [`WeierstrassCurve.IsSemistableModel`](def/FLTPrelim_Modularity.html#L85), i.e. no prime dividing $\Delta_W$ divides $c_4(W)$. Two hypotheses present the mod-$p$ representation of $W$: the $p$-torsion submodule $\mathrm{torsionBy}_{\mathbb{Z}}\,p$ of the group of points of $W$ base-changed along $\mathbb{Z} \to \mathbb{Q}$ and then to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` has exactly $p^2$ elements (`hcard₁`), and the induced monoid homomorphism `galoisRepModuleEnd` from $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ to the $\mathbb{Z}/p$-endomorphisms of that torsion module satisfies [`GaloisFactorsThroughFiniteLevel`](def/GaloisRep_Residual.html#L17), i.e. there is a finite-dimensional intermediate field $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every automorphism fixing $L$ pointwise acts as the identity (`hker`). It is further assumed that `W.ModRepIsIrreducible p` holds — the project's irreducibility predicate for this representation, left here by name. Let $M$ be squarefree and $q$ a prime with $q \neq p$, $q \mid M$ and $q^2 \nmid M$. Assume the residual representation `residualGaloisRepOf p hcard₁ hker` of the base-changed curve is unramified at $q$ in the project's sense: for every valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over the prime $q$, every element of the inertia subgroup of $A$ over $\mathbb{Q}$ acts trivially. Finally assume `W.IsResiduallyModularOfLevel p M`: there are a normalised eigenform $f$ of weight $2$ on $\Gamma_0(M)$ and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$ such that for every prime $\ell$ which is a good prime for $W$, does not divide $M$ and differs from $p$, there is an algebraic integer $a$ with $a = a_\ell(f)$ in $\mathbb{C}$ and $a \equiv a_\ell(W) \pmod{\mathfrak{m}}$, where $a_\ell(W)$ is `W.apOfModel ℓ`. The conclusion is `W.IsResiduallyModularOfLevel p (M / q)`, the same statement with level the natural-number quotient $M/q$.
--
--   This is Ribet's level-lowering theorem in the shape used on the Frey–Serre–Ribet route, specialised to a prime $q$ exactly dividing a squarefree level: no congruence condition on $q$ modulo $p$ is imposed, both the case $q \equiv 1 \pmod p$ and its complement being covered. Relative to the textbook statement, residual modularity is not phrased as the existence of a representation attached to a newform but as the concrete congruence, modulo a maximal ideal above $p$ of the algebraic integers, between prime-indexed Fourier coefficients of a normalised weight-$2$ eigenform on $\Gamma_0(M)$ and the Frobenius traces `W.apOfModel ℓ` of an integral Weierstrass model; semistability is the elementary divisibility condition on $\Delta_W$ and $c_4(W)$, and the mod-$p$ representation is presented by the two bookkeeping hypotheses `hcard₁` and `hker`. It is the curve-level core of the level-lowering step: it is used by [`FreyPackage.level_lowering_odd_prime_of_conductorLevel`](thm.html#FreyPackage.level_lowering_odd_prime_of_conductorLevel) and by the two theorems that strip the level of a residually modular curve down to the minimal squarefree level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf.lean

import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem WeierstrassCurve.isResiduallyModularOfLevel_div_of_isUnramifiedAt_sqf
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
    (hres : W.IsResiduallyModularOfLevel p M) :
    W.IsResiduallyModularOfLevel p (M / q) := by sorry
