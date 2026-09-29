-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_and_pow_eq_and_apply_ne
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_and_pow_eq_and_apply_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/7d5cf29d-85aa-5aaa-8ae5-d0479dfa3ef4
-- title:
--   Inertia element with trivial tame character moving a λ-th root of π
-- statement:
--   Let $q$ be a prime and let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `P.LiesOverPrime q`, that is, the image of $q$ in $\overline{\mathbb{Q}}$ lies in the nonunits of $P$. Let $\pi \in \overline{\mathbb{Q}}$ satisfy $\pi^{q^2-1} = q$ (the exponent being the truncated natural-number difference), and let $\lambda$ be a prime with $q \neq \lambda$. Then there exists an automorphism $\tau \in \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ such that: (i) $\tau$ lies in `P.inertiaSubgroupIn ℚ`, the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $P$ under the inclusion of the decomposition subgroup; (ii) the tame character of $\tau$ with respect to $\pi$ is trivial, where `P.tameCharacter π τ` denotes the residue in the residue field of $P$ of $\tau(\pi)/\pi$ when this quotient lies in $P$, and $0$ otherwise; and (iii) there is an $r \in \overline{\mathbb{Q}}$ with $r^{\lambda} = \pi$ and $\tau(r) \neq r$, so that $\tau$ moves some $\lambda$-th root of $\pi$.
--
--   This is the standard surjectivity of tame inertia at $q$ onto the $n$-th roots of unity for $q \nmid n$, packaged in the form needed downstream: an inertia element acting trivially on $\pi$ through the tame character but nontrivially on a $\lambda$-th root of $\pi$. It supplies the hypothesis on covering automorphisms in the semistable-covering statements [`ModularCurve.FullLevel.telescope_frame_of_semistableCovering`](thm.html#ModularCurve.FullLevel.telescope_frame_of_semistableCovering) and its specialisations at $q = 2$ and $q = 3$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_and_pow_eq_and_apply_ne.lean

import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_and_pow_eq_and_apply_ne
    (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ))
    (lam : ℕ) [Fact lam.Prime] (hqlam : q ≠ lam) :
    ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, τ ∈ P.inertiaSubgroupIn ℚ ∧ P.tameCharacter π τ = 1 ∧
      ∃ r : AlgebraicClosure ℚ, r ^ lam = π ∧ τ r ≠ r := by sorry
