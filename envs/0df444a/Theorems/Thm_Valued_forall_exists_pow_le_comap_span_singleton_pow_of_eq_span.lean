-- Prove2me | Theorems.Thm_Valued_forall_exists_pow_le_comap_span_singleton_pow_of_eq_span
-- name    : Valued.forall_exists_pow_le_comap_span_singleton_pow_of_eq_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/548a447f-1c9a-5f06-8414-a8a936d6cdd6
-- title:
--   Adic continuity of ev from valuations of generators
-- statement:
--   Let $B$ be a commutative ring, $K$ a field carrying a valuation $v$ with values in a linearly ordered commutative group with zero $\Gamma_0$, and let $\mathcal{O}[K]$ denote the associated valuation subring $\{x \in K : v(x) \le 1\}$. Given an ideal $\mathfrak{m}$ of $B$, a ring homomorphism $\mathrm{ev} : B \to \mathcal{O}[K]$, and a subset $G \subseteq B$ with $\mathfrak{m} = \operatorname{span} G$; given further an element $\delta \in \Gamma_0$ such that $v(\mathrm{ev}\,g) \le \delta$ for every $g \in G$, an element $\varpi \in \mathcal{O}[K]$ whose image in $K$ is nonzero, and the hypothesis that for every $k \in \mathbb{N}$ there exists $n \in \mathbb{N}$ with $\delta^{n} \le v(\varpi)^{k}$; then for every $k \in \mathbb{N}$ there exists $n \in \mathbb{N}$ such that $\mathfrak{m}^{n}$ is contained in the preimage under $\mathrm{ev}$ of the ideal $(\varpi)^{k}$ of $\mathcal{O}[K]$, i.e. $\mathrm{ev}(\mathfrak{m}^{n}) \subseteq (\varpi)^{k}$. No hypothesis that $\delta < 1$ or that $\varpi$ generates the maximal ideal is imposed; the archimedean-type comparison hypothesis on $\delta$ and $v(\varpi)$ carries all of that weight.
--
--   This is the continuity statement needed to extend an evaluation homomorphism $B \to \mathcal{O}[K]$ to the $\mathfrak{m}$-adic completion of $B$: bounding the valuations of a generating set of $\mathfrak{m}$ suffices to make $\mathrm{ev}$ continuous for the $\mathfrak{m}$-adic topology on the source and the $\varpi$-adic topology on the target. It is used in the analysis of prolongations of place specialisations on modular curves, in particular to produce a homomorphism from an adic completion of a node ring compatible with a given evaluation, and in the resulting bounds on numbers of prolongations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Valued_forall_exists_pow_le_comap_span_singleton_pow_of_eq_span.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Valued in

theorem Valued.forall_exists_pow_le_comap_span_singleton_pow_of_eq_span
    {B : Type*} [CommRing B] {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [hK : Valued K Γ₀]
    (𝔪 : Ideal B) (ev : B →+* 𝒪[K]) (G : Set B) (hG : 𝔪 = Ideal.span G)
    (δ : Γ₀) (hδ : ∀ g ∈ G, Valued.v (ev g : K) ≤ δ) (ϖ : 𝒪[K]) (hϖ0 : (ϖ : K) ≠ 0)
    (harch : ∀ k : ℕ, ∃ n : ℕ, δ ^ n ≤ Valued.v (ϖ : K) ^ k) :
    ∀ k : ℕ, ∃ n : ℕ, 𝔪 ^ n ≤ (Ideal.span {ϖ} ^ k).comap ev := by sorry
