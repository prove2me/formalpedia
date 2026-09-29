-- Prove2me | Theorems.Thm_WeierstrassCurve_isModularModelOfLevel_conductorLevel_of_not_cube_dvd_of_modRepIsIrreducible_of_factorization_eq
-- name    : WeierstrassCurve.isModularModelOfLevel_conductorLevel_of_not_cube_dvd_of_modRepIsIrreducible_of_factorization_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/a5def1bb-b3c5-58f4-a04f-992e8d954efa
-- title:
--   Descent to the conductor level for a semistable model
-- statement:
--   Let $W$ be a Weierstrass model over $\mathbb{Z}$, with discriminant $\Delta$ and invariant $c_4$, and suppose $W$ is a semistable model in the project's sense: for every prime $\ell$ with $\ell \mid \Delta$ one has $\ell \nmid c_4$. Let $N$ be a natural number and let $p$ be a prime (supplied as a `Fact` instance) with $p \neq 2$, and assume the project's irreducibility predicate `ModRepIsIrreducible` holds for $W$ at $p$, i.e. the $p$-torsion submodule of the points of $W$ base-changed to an algebraic closure of $\mathbb{Q}$ is nontrivial and its only $\mathbb{Z}/p$-submodules stable under $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ are $\bot$ and $\top$. Assume further: (i) the exponent of $p$ in $N$ equals the exponent of $p$ in $W.\mathtt{conductorLevel}$, which is by definition the radical of $|\Delta|$, i.e. the squarefree product of the primes dividing $\Delta$ (not the conductor of the associated elliptic curve); (ii) $W$ is modular of level $N$, meaning there is a normalised eigenform $f$ of weight $2$ on $\Gamma_0(N)$ — normalised in the sense of the project's structure recording $a_1 = 1$ and the multiplicativity and prime-power recursions for the $q$-expansion coefficients — such that for every prime $q$ with $q \nmid \Delta$ and $q \nmid N$ the $q$-th coefficient of $f$ equals the trace of Frobenius $a_q$ of the reduction of $W$ modulo $q$; (iii) every prime dividing $\Delta$ divides $N$; and (iv) no cube of a prime divides $N$ (which in particular forces $N \neq 0$). Then $W$ is modular of level $W.\mathtt{conductorLevel}$ in the same sense.
--
--   This is a form of Ribet's level-lowering theorem, specialised to the situation needed for the Frey curve: the level is brought down from an auxiliary $N$ satisfying a cube-free condition to the radical of the discriminant of the given integral model. It differs from the textbook statement in several ways: modularity is expressed as the existence of a weight-$2$ normalised eigenform on $\Gamma_0$ whose coefficients at primes of good reduction away from the level match the Frobenius traces of the given Weierstrass model, the target level is the radical of the model's discriminant rather than the conductor of the curve, and the $p$-part of $N$ is assumed to agree already with the $p$-part of that radical. It is used to prove the variant in which the hypothesis on the $p$-part of $N$ is replaced by the weaker condition $p^2 \nmid N$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isModularModelOfLevel_conductorLevel_of_not_cube_dvd_of_modRepIsIrreducible_of_factorization_eq.lean

import Definitions.Def_WeierstrassCurve_ConductorLevel
import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem
WeierstrassCurve.isModularModelOfLevel_conductorLevel_of_not_cube_dvd_of_modRepIsIrreducible_of_factorization_eq
    (W : WeierstrassCurve ℤ) (hss : W.IsSemistableModel) (N : ℕ)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hirr : W.ModRepIsIrreducible p)
    (hp : N.factorization p = W.conductorLevel.factorization p)
    (hN : W.IsModularModelOfLevel N) (hbad : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W.Δ → ℓ ∣ N)
    (hN3 : ∀ q : ℕ, q.Prime → ¬ q ^ 3 ∣ N) :
    W.IsModularModelOfLevel W.conductorLevel := by sorry
