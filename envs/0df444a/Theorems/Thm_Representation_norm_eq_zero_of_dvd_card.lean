-- Prove2me | Theorems.Thm_Representation_norm_eq_zero_of_dvd_card
-- name    : Representation.norm_eq_zero_of_dvd_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/9f878d00-61af-5be2-a22f-daacd648fa14
-- title:
--   Vanishing of the norm of a cyclic group in characteristic p
-- statement:
--   Let $k$ be a field, $Q$ a finite group, $V$ a $k$-vector space, and $\rho : Q \to \mathrm{GL}_k(V)$ a $k$-linear representation of $Q$ on $V$. Let $p$ be a natural number which is the characteristic of $k$, let $g \in Q$ be such that every element of $Q$ lies in the subgroup of integer powers of $g$ (so $Q$ is cyclic with generator $g$), and let $d$ be a natural number with $\rho(g)^d = 1$ as an endomorphism of $V$. Assume $p\,d$ divides $\lvert Q\rvert$; since $\lvert Q \rvert \ge 1$ this forces $p > 0$ and $d > 0$. Then the norm endomorphism of $\rho$, namely the sum $\sum_{x \in Q} \rho(x)$ over all elements of $Q$, is the zero endomorphism of $V$.
--
--   This is the standard vanishing criterion for the norm (trace) element of a finite cyclic group acting on a vector space in characteristic $p$: it suffices that the index of the kernel-level $p\,d$ divides the group order, where $d$ kills the image of the generator. It is used in the computation of dimensions of unramified cohomology classes at finite levels with cyclic quotient, being cited by [`ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth`](thm.html#ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth) and by [`groupCohomology.invariants_add_dualTwist_le_finrank_continuousClasses`](thm.html#groupCohomology.invariants_add_dualTwist_le_finrank_continuousClasses).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_norm_eq_zero_of_dvd_card.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

theorem Representation.norm_eq_zero_of_dvd_card {k Q V : Type*} [Field k] [Group Q] [Fintype Q] [AddCommGroup V] [Module k V] (ρ : Representation k Q V)
    (p : ℕ) [CharP k p] {g : Q} (hg : ∀ x : Q, x ∈ Subgroup.zpowers g) {d : ℕ} (hd : ρ g ^ d = 1) (hpd : p * d ∣ Fintype.card Q) :
    ρ.norm = 0 := by sorry
