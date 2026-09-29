-- Prove2me | Theorems.Thm_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D
-- name    : RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/1444b5f7-4748-5313-b180-4b026d243783
-- title:
--   Formal étaleness of the coordinate map A[X]→ S, X↦ t
-- statement:
--   Let $A$ and $S$ be commutative rings and let $i : A \to S$ be a ring homomorphism which is formally smooth in the sense of `RingHom.FormallySmooth`, and let $t \in S$. Regard $S$ as an $A$-algebra via $i$, and assume that the module of Kähler differentials $\Omega_{S/A}$ is free of rank one on the class of $t$ in the strong sense that for every $\omega \in \Omega_{S/A}$ there is a unique $s \in S$ with $\omega = s \cdot \mathrm{d}t$, where $\mathrm{d} =$ `KaehlerDifferential.D A S`. Then the evaluation homomorphism $\mathrm{eval}_2(i,t) : A[X] \to S$, which sends a polynomial $P = \sum a_n X^n$ to $\sum i(a_n) t^n$, is both formally smooth and formally unramified as a ring homomorphism, i.e. the conclusion is the conjunction of `FormallySmooth` and `FormallyUnramified` for `Polynomial.eval₂RingHom i t`. No finiteness or Noetherian hypotheses are imposed on $A$, $S$ or $i$.
--
--   This is the infinitesimal criterion identifying a formally smooth $A$-algebra with one-dimensional free differentials as a formally étale $A[X]$-algebra: a coordinate $t$ whose differential freely generates $\Omega_{S/A}$ makes $S$ formally étale over the polynomial ring in that coordinate. It is used to produce formally smooth and unramified presentations, being cited in the treatment of quotients by a single relation ([`Algebra.FormallySmooth.quotient_span_singleton_of_existsUnique_eq_smul_D`](thm.html#Algebra.FormallySmooth.quotient_span_singleton_of_existsUnique_eq_smul_D)) and in the two-generator, maximal-ideal version [`RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_maximalIdeal_eq_span_pair`](thm.html#RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_maximalIdeal_eq_span_pair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RingHom_formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem RingHom.formallySmooth_and_formallyUnramified_eval2RingHom_of_existsUnique_eq_smul_D
    {A S : Type} [CommRing A] [CommRing S] (i : A →+* S) (hi : i.FormallySmooth) (t : S)
    (hdt : letI : Algebra A S := i.toAlgebra;
      ∀ ω : KaehlerDifferential A S, ∃! s : S, ω = s • KaehlerDifferential.D A S t) :
    (Polynomial.eval₂RingHom i t).FormallySmooth ∧ (Polynomial.eval₂RingHom i t).FormallyUnramified := by sorry
