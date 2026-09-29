-- Prove2me | Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_mul_ordCompl_of_inertia_moves_torsion_of_two_dvd_of_eq_three
-- name    : WeierstrassCurve.isResiduallyModularOfLevel_mul_ordCompl_of_inertia_moves_torsion_of_two_dvd_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/527e2eeb-6f64-506f-8ed7-9c8982beaeb3
-- title:
--   Level-p residual modularity from any level, p=3
-- statement:
--   Let $p$ be a natural number that is prime, subject to the hypotheses $p \neq 2$ and $p = 3$ (the former redundant given the latter, both being carried as binders), and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$ which is a semistable model in the sense that for every prime $q$ dividing $\Delta_W$ one has $q \nmid c_4(W)$. Assume the mod-$p$ representation of $W$ is irreducible in the sense that the $p$-torsion of the group of points of $W$ base-changed to $\mathbb{Q}$ over $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` is nontrivial and every $\mathbb{Z}/p$-submodule of it stable under the Galois action is $\bot$ or $\top$. Let $M$ be a nonzero natural number such that: if $p^2 \mid M$ then $M$ is even; if $p^2 \mid M$ then for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ (so $A$ lies over $p$), the only $p$-torsion point of $W$ over $\overline{\mathbb{Q}}$ fixed by every element of the inertia subgroup of $A$ over $\mathbb{Q}$ is $0$. Assume finally that $W$ is residually modular of level $M$, i.e. there are a weight-$2$ cusp form $f$ on $\Gamma_0(M)$ which is a normalised eigenform (its $q$-expansion coefficients satisfy $a_1 = 1$, multiplicativity at coprime arguments and the usual Hecke recursions at prime powers, in the two regimes $p' \nmid M$ and $p' \mid M$) and a maximal ideal $\mathfrak{m}$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ containing $p$, such that for every prime $\ell$ with $\ell \nmid \Delta_W$, $\ell \nmid M$ and $\ell \neq p$ the $\ell$-th coefficient of $f$ lies in that integral closure and is congruent mod $\mathfrak{m}$ to the trace of Frobenius of the reduction of $W$ modulo $\ell$. Then $W$ is residually modular of level $p \cdot \bigl(M / p^{\operatorname{ord}_p M}\bigr)$, that is, at $p$ times the prime-to-$p$ part of $M$.
--
--   This is the level-optimisation step at the prime $3$: the power of $p$ occurring in the level of the congruent eigenform can be reduced to exactly $p^1$, under a semistability hypothesis on the integral model, irreducibility of the mod-$p$ representation, and (when $p^2$ still divides the level) the requirement that inertia above $p$ fixes no nonzero $p$-torsion point. It feeds the construction of the Hecke–Galois datum and the minimal-level statement on the $p = 3$ branch of the Fermat argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_mul_ordCompl_of_inertia_moves_torsion_of_two_dvd_of_eq_three.lean

import Definitions.Def_FLTPrelim_ModularRep
import Mathlib.Data.Nat.Factorization.Defs
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped WeierstrassCurve.Affine

theorem WeierstrassCurve.isResiduallyModularOfLevel_mul_ordCompl_of_inertia_moves_torsion_of_two_dvd_of_eq_three (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p = 3) (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0) (hW : W.IsSemistableModel) (hirr : W.ModRepIsIrreducible p) {M : ℕ} [NeZero M]
    (h2M : p ^ 2 ∣ M → 2 ∣ M)
    (hns : p ^ 2 ∣ M →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point p,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) → x = 0)
    (hres : W.IsResiduallyModularOfLevel p M) : W.IsResiduallyModularOfLevel p (p * (M / p ^ (M.factorization p))) := by sorry
