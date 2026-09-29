-- Prove2me | Theorems.Thm_Subring_exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring
-- name    : Subring.exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/1cf0f0ec-5e1a-520c-8586-b8a30897101b
-- title:
--   An invariant element regular on a finite family, with a pole along V
-- statement:
--   Let $k$ and $K$ be fields with $K$ a $k$-algebra, let $G$ be a subgroup of the group $K \simeq_{\mathrm{alg}[k]} K$ of $k$-algebra automorphisms of $K$ whose underlying set is finite, and let $B$ be a subring of $K$ such that $\sigma f \in B$ for every $\sigma \in G$ and every $f \in B$. Let $V$ be a valuation subring of $K$ with $B \subseteq V$, and assume there is some $b \in B$ with $b \neq 0$ whose image in $V$ lies in the maximal ideal of $V$. Let $E$ be a finite set of subrings of $K$ such that each $O \in E$ is a local ring, each $O \in E$ contains $B$, and $E$ is stable under $G$ in the sense that for every $\sigma \in G$ and every $O \in E$ there is $O' \in E$ with $f \in O' \iff \sigma f \in O$ for all $f \in K$. Assume furthermore that the family $E$ is separated from $V$ over $B$: for each $O \in E$ there is $b \in B$ whose image in $V$ lies in the maximal ideal of $V$ and whose image in $O$ is a unit. Then there exists $f \in K$ with $\sigma f = f$ for all $\sigma \in G$, with $f \in O$ for every $O \in E$, and with $f \notin V$.
--
--   In the geometric situation for which it is designed, $B$ is a common affine chart, the members of $E$ are the local rings at a finite $G$-stable set of closed points, and $V$ is the valuation ring of a divisor (for instance a component of a special fibre) avoiding those points; the conclusion produces a $G$-invariant rational function regular at all the points of the family but with a pole along the divisor. It is used in the construction of rigid charts and of traces on modular curves of full level, by [`ModularCurve.FullLevel.pernodeConclusion_traces_of_rigidDescentHyps`](thm.html#ModularCurve.FullLevel.pernodeConclusion_traces_of_rigidDescentHyps) and the two related statements for the residue characteristics $2$ and $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subring_exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem Subring.exists_forall_algEquiv_apply_eq_and_forall_mem_and_not_mem_valuationSubring
    {k K : Type} [Field k] [Field K] [Algebra k K]
    (G : Subgroup (K ≃ₐ[k] K)) (hGfin : Finite ↥G)
    (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (V : ValuationSubring K) (hBV : ∀ f : K, f ∈ B → f ∈ V)
    (hp : ∃ (b : K) (hb : b ∈ B), b ≠ 0 ∧ (⟨b, hBV b hb⟩ : ↥V) ∈ maximalIdeal ↥V)
    (E : Finset (Subring K)) (hEloc : ∀ O ∈ E, IsLocalRing ↥O) (hBE : ∀ O ∈ E, ∀ f : K, f ∈ B → f ∈ O)
    (hEG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ O ∈ E, ∃ O' ∈ E, ∀ f : K, f ∈ O' ↔ σ f ∈ O)
    (hsep : ∀ (O : Subring K) (hO : O ∈ E), ∃ (b : K) (hb : b ∈ B),
      (⟨b, hBV b hb⟩ : ↥V) ∈ maximalIdeal ↥V ∧ IsUnit (⟨b, hBE O hO b hb⟩ : ↥O)) :
    ∃ f : K, (∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f) ∧ (∀ O ∈ E, f ∈ O) ∧ f ∉ V := by sorry
