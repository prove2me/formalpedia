-- Prove2me | Theorems.Thm_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd
-- name    : WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/00c45b8e-180e-5702-b9a4-d5ed26896e05
-- title:
--   Modularity lifting at p∈{3,5} for p²∤ M₀
-- statement:
--   Let $p$ be a natural number equal to $3$ or to $5$, and let $W$ be a Weierstrass curve over $\mathbb{Z}$ satisfying: $W.\Delta\neq 0$; `W.IsSemistableModel`, i.e. no prime $q$ with $q\mid\Delta(W)$ also divides $c_4(W)$; and `W.ModRepIsIrreducible p`, i.e. the module of $p$-torsion points of $W$ base-changed to $\mathbb{Q}$ over an algebraic closure $\overline{\mathbb{Q}}$ is nontrivial and its only $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$-stable $\mathbb{Z}/p$-submodules are $0$ and the whole module. Let $M_0$ be a nonzero natural number such that `W.IsResiduallyModularOfLevel p M₀` holds: there are a weight-two cusp form $f$ on $\Gamma_0(M_0)$ which is a normalised eigenform in the project's $q$-expansion sense (first coefficient $1$, multiplicativity at coprime indices, and the two Hecke recursions at primes dividing and not dividing the level) and a maximal ideal $\mathfrak m$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ with $p\in\mathfrak m$, such that for every prime $\ell$ with $\ell\nmid\Delta(W)$, $\ell\nmid M_0$ and $\ell\neq p$ the coefficient $a_\ell(f)$ is an algebraic integer congruent to $a_\ell(W)=\ell+1-\#W(\mathbb{F}_\ell)$ modulo $\mathfrak m$. Assume moreover two divisibility conditions on this witness level: $p^2\nmid M_0$, and $q^3\nmid M_0$ for every prime $q\neq p$. The conclusion is [`Mlc1IsModularModelOfExactConductorLevel W`](def/WeierstrassCurve_Mlc1RowStatement.html#L9): there exists a positive squarefree $N$ such that a prime $q$ divides $N$ if and only if $q\mid\Delta(W)$, together with a normalised weight-two eigenform on $\Gamma_0(N)$ whose coefficient at every prime $\ell$ with $\ell\nmid\Delta(W)$ and $\ell\nmid N$ equals $a_\ell(W)$.
--
--   This is the modularity lifting theorem ($R=\mathbb T$) of Wiles and Taylor–Wiles at $p=3$ and $p=5$, in the form used on the Fermat route: the input is a residual-modularity witness of an explicitly constrained level $M_0$ (not divisible by $p^2$, and cube-free away from $p$), and the output is modularity at the exact squarefree conductor level, the level being characterised by its prime divisors being exactly the primes dividing the discriminant of the given model. It differs from the textbook statement in that semistability, irreducibility and modularity are the project's model-theoretic notions formulated in terms of $\Delta$, $c_4$, torsion modules and $q$-expansion coefficients, and in that the residual hypothesis comes with the level bounds $p^2\nmid M_0$, $q^3\nmid M_0$ ($q\neq p$) rather than an inertia condition at $p$. It feeds [`WeierstrassCurve.modularity_of_semistableModel`](thm.html#WeierstrassCurve.modularity_of_semistableModel), hence the modularity of Frey curves through [`FreyPackage.modularRepOfConductorLevel`](thm.html#FreyPackage.modularRepOfConductorLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd.lean

import Definitions.Def_WeierstrassCurve_Mlc1RowStatement

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_not_sq_dvd_of_not_cube_dvd (p : ℕ) (hp : p = 3 ∨ p = 5)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p)
    (M₀ : ℕ) [NeZero M₀] (hres₀ : W.IsResiduallyModularOfLevel p M₀)
    (hM₀ : ¬ p ^ 2 ∣ M₀)
    (hM₀3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M₀) :
    Mlc1IsModularModelOfExactConductorLevel W := by sorry
