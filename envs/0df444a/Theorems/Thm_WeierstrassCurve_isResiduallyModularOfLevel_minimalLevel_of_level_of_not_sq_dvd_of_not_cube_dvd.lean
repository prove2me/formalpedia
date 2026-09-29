-- Prove2me | Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_minimalLevel_of_level_of_not_sq_dvd_of_not_cube_dvd
-- name    : WeierstrassCurve.isResiduallyModularOfLevel_minimalLevel_of_level_of_not_sq_dvd_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/8e39617b-6d00-549a-9541-5db5e61629d6
-- title:
--   Lowering a bounded residual-modularity witness to the minimal level
-- statement:
--   Let $p$ be an odd prime and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta(W)\neq 0$ which is a semistable model in the sense that no prime $q$ dividing $\Delta(W)$ divides $c_4(W)$. Write $W_{\mathbb{Q}}$ for the base change of $W$ along $\mathbb{Z}\to\mathbb{Q}$, and assume: the $p$-torsion subgroup of the points of $W_{\mathbb{Q}}$ over an algebraic closure of $\mathbb{Q}$ has cardinality $p^2$ (hypothesis `hcard₁`); the Galois action on this $p$-torsion, as a homomorphism from $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathbb{Z}/p$-module endomorphisms, is trivial on the elements fixing some finite subextension $L/\mathbb{Q}$ (hypothesis `hker`); and this $p$-torsion module is irreducible, i.e. nontrivial and with every Galois-stable $\mathbb{Z}/p$-submodule equal to $\bot$ or $\top$. Let $M_0$ be a nonzero natural number such that $W$ is residually modular mod $p$ of level $M_0$, meaning that there exist a normalised eigenform $f$ of weight $2$ on $\Gamma_0(M_0)$ and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ with $p\in\mathfrak{m}$ such that for every prime $\ell\neq p$ with $\ell\nmid\Delta(W)$ and $\ell\nmid M_0$ the $\ell$-th $q$-expansion coefficient of $f$ is an algebraic integer congruent to $a_\ell(W)=\#\mathbb{F}_\ell+1-\#W_{\mathbb{F}_\ell}$ modulo $\mathfrak{m}$. Assume further $p^2\nmid M_0$ and $q^3\nmid M_0$ for every prime $q\neq p$. Then there is a squarefree $N$ such that $W$ is residually modular mod $p$ of level $N$, such that for every prime $q\neq p$ one has $q\mid N$ if and only if the residual representation $\bar\rho$ attached to the $p$-torsion by `residualGaloisRepOf` (using `hcard₁` and `hker`) is ramified at $q$ — that is, some valuation subring $A$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$ has an element of its inertia subgroup over $\mathbb{Q}$ acting nontrivially — and such that $p\mid N$ if and only if $p\mid\Delta(W)$ or $p\nmid a_p(W)$.
--
--   This is the level-lowering step in the Frey-curve argument: from one witness of residual modularity of bounded level (no $p^2$, and cube-free away from $p$) it produces a witness of the minimal squarefree level, whose prime divisors away from $p$ are exactly the primes of ramification of $\bar\rho$ and whose divisibility by $p$ is governed by reduction at $p$. It feeds the construction of the patching datum used further on in the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_minimalLevel_of_level_of_not_sq_dvd_of_not_cube_dvd.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point in

theorem WeierstrassCurve.isResiduallyModularOfLevel_minimalLevel_of_level_of_not_sq_dvd_of_not_cube_dvd
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hW : W.IsSemistableModel)
    (hcard₁ : Nat.card (Submodule.torsionBy ℤ
      ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p) = p ^ 2)
    (hker : GaloisFactorsThroughFiniteLevel
      (WeierstrassCurve.Affine.Point.galoisRepModuleEnd (K := AlgebraicClosure ℚ) ℚ
        (W.map (Int.castRingHom ℚ)) p))
    (hirr : W.ModRepIsIrreducible p)
    (M₀ : ℕ) [NeZero M₀] (hres₀ : W.IsResiduallyModularOfLevel p M₀)
    (hM₀ : ¬ p ^ 2 ∣ M₀)

    (hM₀3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M₀) :
    ∃ N : ℕ, Squarefree N ∧
      (∀ q : ℕ, q.Prime → q ≠ p →
        (q ∣ N ↔ ¬ ((W.map (Int.castRingHom ℚ)).residualGaloisRepOf p hcard₁ hker).IsUnramifiedAt q)) ∧
      (p ∣ N ↔ (¬ W.IsGoodPrimeFor p ∨ ¬ (p : ℤ) ∣ W.apOfModel p)) ∧
      W.IsResiduallyModularOfLevel p N := by sorry
