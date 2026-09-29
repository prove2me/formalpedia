-- Prove2me | Theorems.Thm_TateModule_forall_rep_eq_self_of_rep_eq_self_of_unipotent_of_forall_eq_pow_mul_pow_mul_pow
-- name    : TateModule.forall_rep_eq_self_of_rep_eq_self_of_unipotent_of_forall_eq_pow_mul_pow_mul_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/b3ecd0d2-e9af-52fe-9d12-651a730be24e
-- title:
--   Fixing a tame generator suffices on the Tate module
-- statement:
--   Let $G$ be a group acting on an additive abelian group $V$ by additive maps, let $\ell$ be a prime, let $S$ be a subgroup of $G$ and $\gamma \in G$. Here $\mathtt{TateModule}\ \ell\ V$ is the subgroup of sequences $(z_n)_{n \in \mathbb{N}}$ in $V$ satisfying $\ell^n z_n = 0$ and $\ell\, z_{n+1} = z_n$ for all $n$, and [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) is the resulting monoid homomorphism from $G$ to the $\mathbb{Z}_\ell$-linear endomorphisms of this module, acting componentwise. Two hypotheses are imposed: (U) for all $x, y \in S$, every $n$ and every $v \in V$ with $\ell^n v = 0$, one has $x(yv - v) = yv - v$, i.e. $(x-1)(y-1)$ annihilates the $\ell$-power torsion of $V$; and (T) for every $m \in \mathbb{N}$ and every $\tau \in S$ there exist $j \in \mathbb{N}$ and $x, w \in S$ with $\tau = \gamma^j x^{\ell^m} w^{\ell^m}$. The conclusion: if $z$ is an element of the Tate module with $\gamma z = z$, then $\tau z = z$ for every $\tau \in S$.
--
--   This is the elementary algebraic mechanism behind the statement that, for the $\ell$-adic Tate module of a semistable abelian variety, a vector fixed by one lift of a topological generator of tame inertia is fixed by the whole inertia subgroup: hypothesis (U) abstracts the condition $(\sigma-1)(\tau-1)=0$ on torsion coming from Grothendieck's description of inertia on semistable reduction, and (T) abstracts pro-cyclicity of tame inertia modulo $\ell^m$-th powers. It is used in the analysis of inertia invariants on the Tate module arising in the study of modular curves and their Jacobians, through [`ModularCurve.JH.exists_pow_smul_mem_span_inertia_sub_sup_old_of_rep_eq_self_tateModule_of_dvd_of_not_sq_dvd`](thm.html#ModularCurve.JH.exists_pow_smul_mem_span_inertia_sub_sup_old_of_rep_eq_self_tateModule_of_dvd_of_not_sq_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_forall_rep_eq_self_of_rep_eq_self_of_unipotent_of_forall_eq_pow_mul_pow_mul_pow.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TateModule.forall_rep_eq_self_of_rep_eq_self_of_unipotent_of_forall_eq_pow_mul_pow_mul_pow
    {G V : Type} [Group G] [AddCommGroup V] [DistribMulAction G V]
    (ℓ : ℕ) [Fact ℓ.Prime] (S : Subgroup G) (γ : G)

    (hU : ∀ x ∈ S, ∀ y ∈ S, ∀ (n : ℕ) (v : V), ((ℓ ^ n : ℕ) : ℤ) • v = 0 → x • (y • v - v) = y • v - v)

    (hT : ∀ (m : ℕ), ∀ τ ∈ S, ∃ (j : ℕ) (x w : G), x ∈ S ∧ w ∈ S ∧ τ = γ ^ j * x ^ (ℓ ^ m) * w ^ (ℓ ^ m))
    (z : TateModule ℓ V) (hz : TateModule.rep ℓ V G γ z = z) :
    ∀ τ ∈ S, TateModule.rep ℓ V G τ z = z := by sorry
