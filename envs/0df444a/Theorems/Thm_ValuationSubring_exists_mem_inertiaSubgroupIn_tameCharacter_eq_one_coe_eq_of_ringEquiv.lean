-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/4e8ee327-61ed-55cd-9db0-605b60d9847e
-- title:
--   Place-stabilising ring automorphisms as inertia elements of trivial tame character
-- statement:
--   Let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $\pi \in \overline{\mathbb{Q}}$ be non-zero, and let $\sigma$ be a ring automorphism of $\overline{\mathbb{Q}}$ (a `RingEquiv`, with no $\mathbb{Q}$-linearity assumed) such that: for every $a \in \overline{\mathbb{Q}}$ one has $a \in P$ if and only if $\sigma a \in P$; $\sigma \pi = \pi$; and for every $a \in P$ and every proof that $\sigma a \in P$, the residue of $\sigma a$ in the residue field of the local ring $P$ equals the residue of $a$. The conclusion asserts the existence of a $\mathbb{Q}$-algebra automorphism $\tau$ of $\overline{\mathbb{Q}}$ such that $\tau$ lies in `P.inertiaSubgroupIn ℚ`, that is, in the image of the inertia subgroup of $P$ under the inclusion of the decomposition subgroup $\mathrm{Stab}(P) \le \overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$; that `P.tameCharacter π τ`, defined as the residue of $\tau\pi/\pi$ in the residue field of $P$ when $\tau\pi/\pi \in P$ and as $0$ otherwise, equals $1$; and that $\tau a = \sigma a$ for every $a \in \overline{\mathbb{Q}}$.
--
--   This is the bookkeeping step converting a ring automorphism of $\overline{\mathbb{Q}}$ that stabilises a place $P$, fixes a chosen element $\pi$ and acts trivially on the residue field into an element of the inertia subgroup at $P$ whose tame character at $\pi$ is trivial. It is used to discharge the hypotheses on the covering set of automorphisms in the semistable-covering results for modular curves of full level, namely [`ModularCurve.FullLevel.telescope_frame_of_semistableCovering`](thm.html#ModularCurve.FullLevel.telescope_frame_of_semistableCovering) and its specialisations at $2$ and $3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv.lean

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv
    (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ) (hπ0 : π ≠ 0)
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)
    (hσP : ∀ a : AlgebraicClosure ℚ, a ∈ P ↔ σ a ∈ P) (hσπ : σ π = π)
    (hσres : ∀ (a : P) (h : σ (a : AlgebraicClosure ℚ) ∈ P),
      IsLocalRing.residue P ⟨σ (a : AlgebraicClosure ℚ), h⟩ = IsLocalRing.residue P a) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ P.inertiaSubgroupIn ℚ ∧ P.tameCharacter π τ = 1 ∧
      ∀ a, τ a = σ a := by sorry
