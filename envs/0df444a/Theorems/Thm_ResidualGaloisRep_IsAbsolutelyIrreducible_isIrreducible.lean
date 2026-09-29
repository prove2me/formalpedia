-- Prove2me | Theorems.Thm_ResidualGaloisRep_IsAbsolutelyIrreducible_isIrreducible
-- name    : ResidualGaloisRep.IsAbsolutelyIrreducible.isIrreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/9654f5fb-9434-53c2-b183-180e8fcce0f1
-- title:
--   Absolute irreducibility implies irreducibility
-- statement:
--   Let $k$ be a field and let $\rho$ be a residual Galois representation over $k$ in the sense of the project's structure [`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22): a $k$-vector space $V$ with $\operatorname{finrank}_k V = 2$, a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ to $\operatorname{End}_k V$, subject to the condition that $\rho$ factors through a finite level, i.e. there is an intermediate field $L$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}/\mathbb{Q}$ with $L/\mathbb{Q}$ finite-dimensional such that $\rho(\sigma) = 1$ for every automorphism $\sigma$ fixing $L$ pointwise. Assume $\rho$ is absolutely irreducible, which by definition means that the base change of $\rho$ to $\mathrm{AlgebraicClosure}\ k$ — the space $\mathrm{AlgebraicClosure}\ k \otimes_k V$ with the operators $\rho(\sigma)$ base-changed — is irreducible, that is, every submodule of the base-changed space stable under all base-changed $\rho(\sigma)$ equals $\bot$ or $\top$. The conclusion is that $\rho$ itself is irreducible: every $k$-submodule $W \subseteq V$ such that $\rho(\sigma)x \in W$ for all $\sigma$ and all $x \in W$ is either $\bot$ or $\top$.
--
--   This is the elementary implication that absolute irreducibility of a two-dimensional residual representation of the absolute Galois group of $\mathbb{Q}$ is stronger than irreducibility over the coefficient field itself. It is used where a hypothesis of absolute irreducibility must be fed into arguments that only require irreducibility, namely in the statements about newforms and about the level-lowering step for the Frey curve that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_IsAbsolutelyIrreducible_isIrreducible.lean

import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ResidualGaloisRep.IsAbsolutelyIrreducible.isIrreducible {k : Type} [Field k] {ρ : ResidualGaloisRep k}
    (h : ρ.IsAbsolutelyIrreducible) : ρ.IsIrreducible := by sorry
