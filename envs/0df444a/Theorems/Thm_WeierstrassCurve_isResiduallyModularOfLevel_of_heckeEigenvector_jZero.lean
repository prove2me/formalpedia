-- Prove2me | Theorems.Thm_WeierstrassCurve_isResiduallyModularOfLevel_of_heckeEigenvector_jZero
-- name    : WeierstrassCurve.isResiduallyModularOfLevel_of_heckeEigenvector_jZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:05.255932+00:00
-- url     : https://prove2.me/theorems/58b6ac79-8928-5396-8b7f-430189c82d3c
-- title:
--   Residual modularity from a mod p Hecke eigenvector in J₀(N₀)
-- statement:
--   Fix a level $N_0\ge 1$ and a prime $p$, and assume the two project hypotheses on the divisorial Hecke action at level $N_0$: [`ModularCurve.HeckeInputsAll N₀`](def/ModularCurve_HeckeInputsAll.html#L8), which asserts for every prime $\ell$ the input package `HeckeInputsAlong` (integrality of the two degeneracy maps $\alpha,\beta$ between the base-changed modular function fields at levels $N_0$ and $N_0\ell$ over $\overline{\mathbb Q}$, existence of principal divisors at level $N_0\ell$, finiteness along $\alpha$, the fundamental identity along $\beta$ and the pushforward norm formula along $\alpha$) under which `heckeOperatorBar N₀ ℓ` is the correspondence-induced endomorphism of `JZero N₀` rather than $0$; and [`ModularCurve.HeckeOperatorsCommuteBar N₀`](def/ModularCurve_HeckeModule.html#L25), that these endomorphisms commute pairwise. Let $W$ be a Weierstrass cubic over $\mathbb Z$ and let $S$ be a finite set of primes characterised by $\ell\in S\iff \ell\mid N_0\,p\,|\Delta_W|$. Suppose $y\in$ `JZero N₀` $=\mathrm{Pic}^0$ of the base-changed full modular function field of level $N_0$ over $\overline{\mathbb Q}$ satisfies $y\ne 0$, $p\cdot y=0$, and, for the module structure `heckeModuleBar N₀` of $\mathbb T=\mathbb Z[X_\ell]$ on `JZero N₀` obtained by sending $X_\ell$ to `heckeOperatorBar N₀ ℓ`, $(X_\ell-a_\ell(W))\cdot y=0$ for every prime $\ell\notin S$, where $a_\ell(W)=$ `W.apOfModel ℓ` is the trace of Frobenius of the reduction of $W$ modulo $\ell$. Then `W.IsResiduallyModularOfLevel p N₀` holds: there are a weight-two cusp form $f$ on $\Gamma_0(N_0)$ satisfying the project's normalised-eigenform conditions on its $q$-coefficients and a maximal ideal $\mathfrak M$ of the integral closure of $\mathbb Z$ in $\mathbb C$ with $p\in\mathfrak M$, such that for every prime $\ell$ with $\ell\nmid\Delta_W$, $\ell\nmid N_0$ and $\ell\ne p$ there is an algebraic integer $a$ with $a=a_\ell(f)$ in $\mathbb C$ and $a-a_\ell(W)\in\mathfrak M$.
--
--   This is the Hecke-algebra form of the Deligne–Serre lifting lemma: a nonzero $p$-torsion eigenvector in the Jacobian with eigenvalue system $(a_\ell(W))_{\ell\notin S}$ produces a genuine normalised weight-two eigenform whose coefficients are congruent to $a_\ell(W)$ modulo a maximal ideal of $\overline{\mathbb Z}$ above $p$. Unlike the textbook statement, the Jacobian here is the project's divisorial $\mathrm{Pic}^0$ of the base-changed modular function field, the Hecke action is available only under the explicit `HeckeInputsAll` and `HeckeOperatorsCommuteBar` hypotheses, the eigenvalue condition is imposed exactly at the primes outside the set cut out by $N_0\,p\,|\Delta_W|$, and no claim of irreducibility or of the level being optimal is made. It is the terminal step of the level-lowering arguments: the three theorems citing it pass from residual modularity of level $M$ to level $M/q$, both for $q=p$ under a peu ramifiée condition and for $q\ne p$ under unramifiedness with $M$ squarefree.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_isResiduallyModularOfLevel_of_heckeEigenvector_jZero.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.isResiduallyModularOfLevel_of_heckeEigenvector_jZero
    (N₀ : ℕ) [NeZero N₀] {p : ℕ} (hp : p.Prime)
    (hin : ModularCurve.HeckeInputsAll N₀) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N₀)
    (W : WeierstrassCurve ℤ)
    (S : Finset Nat.Primes) (hS : ∀ ℓ : Nat.Primes, ℓ ∈ S ↔ (ℓ : ℕ) ∣ N₀ * p * W.Δ.natAbs)
    (y : ModularCurve.JZero N₀) (hy : y ≠ 0) (hpy : (p : ℤ) • y = 0)
    (heig : ∀ ℓ : Nat.Primes, ℓ ∉ S →
      (letI := ModularCurve.heckeModuleBar N₀;
        (ModularCurve.heckeGen ℓ - MvPolynomial.C (W.apOfModel ℓ)) • y) = 0) :
    W.IsResiduallyModularOfLevel p N₀ := by sorry
