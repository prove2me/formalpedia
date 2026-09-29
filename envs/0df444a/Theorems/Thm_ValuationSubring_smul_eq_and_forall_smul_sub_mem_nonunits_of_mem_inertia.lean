-- Prove2me | Theorems.Thm_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_of_mem_inertia
-- name    : ValuationSubring.smul_eq_and_forall_smul_sub_mem_nonunits_of_mem_inertia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/55e5d84d-a68e-507e-ac1d-e5c09c61d4bc
-- title:
--   Inertia at an ideal fixes the valuation subring centred on it
-- statement:
--   Let $B$ be a commutative ring, $F$ a field and $G$ a group acting on both $B$ and $F$ by ring automorphisms (multiplicative semiring actions). Let $\rho : B \to F$ be a ring homomorphism that is $G$-equivariant, in the sense that $g \cdot \rho(b) = \rho(g \cdot b)$ for all $g \in G$, $b \in B$. Let $\mathfrak{y} \subseteq B$ be an ideal and $P$ a valuation subring of $F$ subject to four hypotheses: (i) $\rho(b) \in P$ for every $b \in B$; (ii) $P$ is centred on $\mathfrak{y}$, i.e. $\rho(b)$ lies in the maximal ideal $P.\mathrm{nonunits}$ of $P$ if and only if $b \in \mathfrak{y}$; (iii) $P$ is the only valuation subring of $F$ with properties (i) and (ii), i.e. any $P'$ satisfying them equals $P$; (iv) every $e \in P$ satisfies $e - \rho(b) \in P.\mathrm{nonunits}$ for some $b \in B$. Then for every $g$ in the inertia subgroup $\mathfrak{y}.\mathrm{inertia}\,G$, that is, every $g \in G$ with $g \cdot b - b \in \mathfrak{y}$ for all $b \in B$, one has both $g \cdot P = P$ (pointwise action on subrings) and $g \cdot e - e \in P.\mathrm{nonunits}$ for every $e \in P$.
--
--   The statement says that inertia at a point is contained in the inertia of the unique place through that point: a group element acting trivially on $B/\mathfrak{y}$ fixes the valuation subring centred on $\mathfrak{y}$ and acts trivially on its residue field. It is used in the bound on the order of inertia groups at supersingular points of an integral model of the modular curve $X_1(N)/\Gamma_0(p)$, where $B$ is a chart ring with its diamond-operator action, $\rho$ the reduction to the function field of a component of the special fibre, and hypotheses (iii)–(iv) express smoothness of that component at the point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_of_mem_inertia.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.smul_eq_and_forall_smul_sub_mem_nonunits_of_mem_inertia
    {B : Type*} [CommRing B] {F : Type*} [Field F] {G : Type*} [Group G]
    [MulSemiringAction G B] [MulSemiringAction G F]
    (ρ : B →+* F) (hρ : ∀ (g : G) (b : B), g • ρ b = ρ (g • b))
    (𝔶 : Ideal B) (P : ValuationSubring F)
    (hP : ∀ b : B, ρ b ∈ P) (hPy : ∀ b : B, ρ b ∈ P.nonunits ↔ b ∈ 𝔶)
    (huniq : ∀ P' : ValuationSubring F,
      (∀ b : B, ρ b ∈ P') → (∀ b : B, ρ b ∈ P'.nonunits ↔ b ∈ 𝔶) → P' = P)
    (hres : ∀ e : ↥P, ∃ b : B, (e : F) - ρ b ∈ P.nonunits)
    (g : G) (hg : g ∈ 𝔶.inertia G) :
    g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits := by sorry
