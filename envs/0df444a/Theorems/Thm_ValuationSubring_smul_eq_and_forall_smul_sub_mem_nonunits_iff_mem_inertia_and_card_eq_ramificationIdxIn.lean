-- Prove2me | Theorems.Thm_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_iff_mem_inertia_and_card_eq_ramificationIdxIn
-- name    : ValuationSubring.smul_eq_and_forall_smul_sub_mem_nonunits_iff_mem_inertia_and_card_eq_ramificationIdxIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/6cb1837a-0ff0-53fe-95c8-81fdccd43a8f
-- title:
--   Inertia of a place equals inertia of its centre, order e
-- statement:
--   Let $R$ and $S$ be commutative rings and $F$ a field, with $S$ an $R$-algebra and $F$ an $S$-algebra which is a fraction field of $S$; let $G$ be a finite group acting on $S$ and on $F$ by ring automorphisms, the two actions being compatible in the sense that $g\cdot\iota(s)=\iota(g\cdot s)$ for all $g\in G$, $s\in S$, where $\iota\colon S\to F$ is the structure map. Let $\mathfrak P$ be an ideal of $S$ and $P$ a valuation subring of $F$ such that: $\iota(S)\subseteq P$; $P$ is centred on $\mathfrak P$, i.e. $\iota(s)$ is a non-unit of $P$ exactly when $s\in\mathfrak P$; and every $e\in P$ can be written as $\iota(s)/\iota(t)$ with $s,t\in S$, $t\notin\mathfrak P$. Two assertions are made. First, for every $g\in G$ one has $g\cdot P=P$ together with $g\cdot e-e\in\mathfrak m_P$ for all $e\in P$ if and only if $g$ lies in `Ideal.inertia` of $\mathfrak P$, i.e. $g\cdot s-s\in\mathfrak P$ for all $s\in S$. Second, under the further assumptions that $G$ is a Galois group for $S/R$, that $R$ and $S$ are Dedekind domains, that $S$ is a finite torsion-free $R$-module, and that $\mathfrak P$ is a maximal ideal lying over an ideal $p$ of $R$ with $(S/\mathfrak P)/(R/p)$ separable, if $p\neq 0$ then the number of $g\in G$ with $g\cdot P=P$ and $g\cdot e-e\in\mathfrak m_P$ for all $e\in P$ equals the common ramification index `Ideal.ramificationIdxIn` of $p$ in $S$.
--
--   This is the dictionary between the inertia group of a place of $F$ (stabilise the valuation ring and act trivially on its residue field) and Hilbert's inertia group of the ideal on which that valuation ring is centred, together with the classical equality $\#I=e$ in the Galois setting with separable residue extension. It is used in the analysis of the special fibre of modular curves, where the width of a component at a point is identified with the ramification index of the corresponding place over the base, and it feeds the statements about discrete valuation rings of fixed points and about the image of the maximal ideal under the fixed-point inclusion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_smul_eq_and_forall_smul_sub_mem_nonunits_iff_mem_inertia_and_card_eq_ramificationIdxIn.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.smul_eq_and_forall_smul_sub_mem_nonunits_iff_mem_inertia_and_card_eq_ramificationIdxIn
    {R S F : Type*} [CommRing R] [CommRing S] [Field F] [Algebra R S] [Algebra S F] [IsFractionRing S F]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G S] [MulSemiringAction G F]
    (hGSF : ∀ (g : G) (s : S), g • algebraMap S F s = algebraMap S F (g • s))
    (𝔓 : Ideal S) (P : ValuationSubring F)
    (hSP : ∀ s : S, algebraMap S F s ∈ P)
    (hcent : ∀ s : S, algebraMap S F s ∈ P.nonunits ↔ s ∈ 𝔓)
    (hfrac : ∀ e : ↥P, ∃ s t : S, t ∉ 𝔓 ∧ (e : F) * algebraMap S F t = algebraMap S F s) :
    (∀ g : G, (g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits) ↔ g ∈ 𝔓.inertia G) ∧
    (∀ [IsGaloisGroup G R S] [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
        [Module.IsTorsionFree R S] (p : Ideal R) [𝔓.LiesOver p] [𝔓.IsMaximal]
        [Algebra.IsSeparable (R ⧸ p) (S ⧸ 𝔓)], p ≠ ⊥ →
      Nat.card {g : G // g • P = P ∧ ∀ e : ↥P, g • (e : F) - e ∈ P.nonunits} = p.ramificationIdxIn S) := by sorry
