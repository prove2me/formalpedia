-- Prove2me | Theorems.Thm_ValuationSubring_mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime
-- name    : ValuationSubring.mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/1071c642-9158-5d0c-b2df-e9b758d816d0
-- title:
--   Automorphisms fixing y stabilise the valuation ring W
-- statement:
--   Let $R$ be a commutative ring, $K$ a field and an $R$-algebra, and let $C \le B$ be $R$-subalgebras of $K$. Let $W$ be a valuation subring of $K$ containing $B$, in the sense that every $f \in B$ lies in $W$; write $\mathfrak m_W$ for the maximal ideal of the local ring $W$. Let $y$ be an ideal of $C$ and $\varpi \in R$ an element whose image in $C$ lies in $y$. Three hypotheses are imposed: (LOC) for every $f \in K$, $f \in W$ if and only if $f h = g$ for some $g, h \in B$ with the image of $h$ in $W$ outside $\mathfrak m_W$; (CEN) for $b \in C$, $b \in y$ if and only if $b$, viewed in $W$, lies in $\mathfrak m_W$; (LEAST) every prime ideal $Q$ of $B$ which contains the image of $\varpi$ and satisfies $Q \cap C = y$ (as an equivalence on elements of $C$ mapped into $B$) contains every $b \in B$ whose image in $W$ lies in $\mathfrak m_W$. Finally let $\tau$ be a ring automorphism of $K$ such that $\tau$ and $\tau^{-1}$ each map $C$ into $C$ and $B$ into $B$, and such that for $b \in C$ with $\tau(b) \in C$ one has $b \in y$ if and only if $\tau(b) \in y$. The conclusion is that for every $f \in K$, $f \in W$ if and only if $\tau(f) \in W$.
--
--   This is the commutative-algebra core of the statement that an automorphism of a function field which preserves two nested subalgebras in both directions and fixes a point $y$ of $\operatorname{Spec} C$ stabilises the valuation ring $W = B_{\mathfrak P}$ attached to the least prime $\mathfrak P$ of $B$ over $y$ containing $\varpi$. It is used in the study of the decomposition and inertia groups acting on Drinfeld-level charts of modular curves, where the level automorphisms fixing a supersingular point are shown to preserve the relevant local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.mem_iff_map_mem_of_ringEquiv_of_isLocalization_of_least_prime
    {R K : Type} [CommRing R] [Field K] [Algebra R K]
    (C B : Subalgebra R K) (hCB : C ≤ B) (W : ValuationSubring K)
    (hBW : ∀ f : K, f ∈ B → f ∈ W)
    (y : Ideal ↥C) (ϖ : R) (hϖy : algebraMap R ↥C ϖ ∈ y)

    (hloc : ∀ f : K, f ∈ W ↔ ∃ g h : ↥B, (⟨(h : K), hBW _ h.2⟩ : ↥W) ∉ IsLocalRing.maximalIdeal ↥W ∧ f * (h : K) = (g : K))

    (hcen : ∀ b : ↥C, b ∈ y ↔ ∃ hb : (b : K) ∈ W, (⟨(b : K), hb⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W)

    (hleast : ∀ Q : Ideal ↥B, Q.IsPrime → algebraMap R ↥B ϖ ∈ Q →
      (∀ b : ↥C, (⟨(b : K), hCB b.2⟩ : ↥B) ∈ Q ↔ b ∈ y) →
      ∀ b : ↥B, (⟨(b : K), hBW _ b.2⟩ : ↥W) ∈ IsLocalRing.maximalIdeal ↥W → b ∈ Q)

    (τ : K ≃+* K)
    (hC : ∀ a : K, a ∈ C → τ a ∈ C) (hC' : ∀ a : K, a ∈ C → τ.symm a ∈ C)
    (hB : ∀ f : K, f ∈ B → τ f ∈ B) (hB' : ∀ f : K, f ∈ B → τ.symm f ∈ B)
    (hy : ∀ (b : ↥C) (hb : τ (b : K) ∈ C), b ∈ y ↔ (⟨τ (b : K), hb⟩ : ↥C) ∈ y) :
    ∀ f : K, f ∈ W ↔ τ f ∈ W := by sorry
