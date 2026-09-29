-- Prove2me | Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isPeuRamifieeAt_of_five_le
-- name    : WeierstrassCurve.isResiduallyModularOfLevel_div_of_isPeuRamifieeAt_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.985064+00:00
-- url     : https://prove2.me/theorems/c15e85f8-842b-560c-8106-e8efe19a2930
-- title:
--   Level lowering at p for primes p ≥ 5
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb Z$ with $\Delta(W) \neq 0$, and let $p \geq 5$ be a prime with $p \neq 2$. Assume: (i) if $p \mid \Delta(W)$ then $p \nmid c_4(W)$; (ii) the mod-$p$ representation of $W$ is irreducible in the sense that the $p$-torsion submodule of the points of $W$ base-changed to $\mathbb Q$ over an algebraic closure of $\mathbb Q$ is nontrivial and its only Galois-stable $\mathbb Z/p$-submodules are $\bot$ and $\top$; (iii) $W$ over $\mathbb Q$ is peu ramifiée at $p$, i.e. $p$ divides $v_p(\Delta(W))$. Let $M > 0$ with $p \mid M$ and $p^2 \nmid M$, and suppose $W$ is residually modular of level $M$ at $p$: there are a cusp form $f$ of weight $2$ on $\Gamma_0(M)$ and a maximal ideal $\mathfrak m$ of the integral closure $\mathcal O$ of $\mathbb Z$ in $\mathbb C$ with $p \in \mathfrak m$, such that $f$ is a normalised eigenform (its $q$-expansion coefficients satisfy $a_1 = 1$, multiplicativity at coprime indices, and the usual recursions at prime powers for primes dividing or not dividing $M$), and for every prime $\ell$ with $\ell \nmid \Delta(W)$, $\ell \nmid M$ and $\ell \neq p$ the coefficient $a_\ell(f)$ lies in $\mathcal O$ and is congruent modulo $\mathfrak m$ to the trace of Frobenius of the reduction of $W$ modulo $\ell$. Then $W$ is residually modular of level $M/p$ at $p$, in the same sense.
--
--   This is the level-lowering step at the residue characteristic: a residual representation which is modular of level $M$ with $p \parallel M$ and which is peu ramifiée (finite) at $p$ is modular of level $M/p$. It is used in the Frey-package argument, in the step [`FreyPackage.mazurPrincipleAtPStep`](thm.html#FreyPackage.mazurPrincipleAtPStep) that removes the factor $p$ from the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_div_of_isPeuRamifieeAt_of_five_le.lean

import Mathlib
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_WeierstrassCurve_PeuRamifiee

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.isResiduallyModularOfLevel_div_of_isPeuRamifieeAt_of_five_le
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (hsemi : (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄)
    (hirr : W.ModRepIsIrreducible p)
    (hfin : (W.map (Int.castRingHom ℚ)).IsPeuRamifieeAt p p)
    {M : ℕ} (hM : 0 < M) (hpM : p ∣ M) (hp2M : ¬ p ^ 2 ∣ M)
    (hmod : W.IsResiduallyModularOfLevel p M) :
    W.IsResiduallyModularOfLevel p (M / p) := by sorry
