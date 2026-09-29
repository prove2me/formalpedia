-- Prove2me | Theorems.Thm_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd
-- name    : WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/5a77d0a8-68f9-596b-b402-d9f0e455065d
-- title:
--   Modularity lifting at p=3 from a prescribed residual level
-- statement:
--   Let $p$ be a natural number with $p=3$, and let $W$ be a Weierstrass curve over $\mathbb{Z}$ subject to: $\Delta(W)\neq 0$; the project's semistability condition `IsSemistableModel`, i.e. no prime dividing $\Delta(W)$ divides $c_4(W)$; and irreducibility of the mod-$p$ representation in the project's sense `ModRepIsIrreducible p`, i.e. the $\mathbb{Z}/p$-module of $p$-torsion points of $W\otimes\mathbb{Q}$ over $\overline{\mathbb{Q}}$ is nontrivial and its only submodules stable under all of $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ are $0$ and the whole module. Let $M_0$ be a nonzero natural number such that $W$ is residually modular of level $M_0$ at $p$: there exist a weight-two cusp form $f$ on $\Gamma_0(M_0)$ normalised and satisfying the Hecke recursions in the project's sense, and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, such that for every prime $\ell$ with $\ell\nmid\Delta(W)$, $\ell\nmid M_0$, $\ell\neq p$ the $\ell$-th $q$-coefficient of $f$ is an algebraic integer congruent to $a_\ell(W)=\ell+1-\#(W\bmod \ell)$ modulo $\mathfrak{m}$. Assume two further conditions on $M_0$: if $p^2\mid M_0$ then for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, every $p$-torsion point of $W$ fixed by the whole inertia subgroup of $A$ over $\mathbb{Q}$ is zero; and for every prime $q\neq p$ one has $q^3\nmid M_0$ (cube-freeness away from $p$ only; $q=p$ is exempt). The conclusion is that there is a positive squarefree $N$ whose prime divisors are exactly the primes dividing $\Delta(W)$, together with a normalised weight-two eigenform on $\Gamma_0(N)$ (in the project's sense) whose $\ell$-th $q$-coefficient equals $a_\ell(W)$ for every prime $\ell$ with $\ell\nmid\Delta(W)$ and $\ell\nmid N$.
--
--   This is the modularity lifting theorem of Wiles and Taylor–Wiles, specialised to the prime $3$ and packaged in the form used along the Frey-curve route: the input is not abstract residual modularity but a residual-modularity witness of an explicit level $M_0$, constrained by a condition on inertia-fixed $3$-torsion when $9\mid M_0$ and by cube-freeness of $M_0$ away from $3$, and the output is modularity at a level which is squarefree with exactly the prime support of the discriminant, rather than merely at some level. The two extra hypotheses on $M_0$ are what the Langlands–Tunnell step supplies at $p=3$ and what the level-lowering at the end of the chain needs. The statement is used, together with the $3$–$5$ switch and the companion lifting theorem for $p\in\{3,5\}$ with $p^2\nmid M_0$, in [`WeierstrassCurve.modularity_of_semistableModel`](thm.html#WeierstrassCurve.modularity_of_semistableModel) and hence in [`FreyPackage.modularRepOfConductorLevel`](thm.html#FreyPackage.modularRepOfConductorLevel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd.lean

import Definitions.Def_WeierstrassCurve_Mlc1RowStatement

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.modularityLiftingAtConductor_threeFive_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd (p : ℕ) (hp : p = 3)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p)
    (M₀ : ℕ) [NeZero M₀] (hres₀ : W.IsResiduallyModularOfLevel p M₀)
    (hns : p ^ 2 ∣ M₀ →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) → x = 0)

    (hM₀3 : ∀ q : ℕ, q.Prime → q ≠ p → ¬ q ^ 3 ∣ M₀) :
    Mlc1IsModularModelOfExactConductorLevel W := by sorry
