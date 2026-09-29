-- Prove2me | Theorems.Thm_Subalgebra_eq_bot_of_moduleFinite_of_forall_ne_maximalIdeal_of_isRegular_pair
-- name    : Subalgebra.eq_bot_of_moduleFinite_of_forall_ne_maximalIdeal_of_isRegular_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/869b572c-d4c0-5f18-816c-8a7909133a8e
-- title:
--   Module-finite overrings of a local ring with a length-two regular sequence
-- statement:
--   Let $B$ be a commutative Noetherian local ring with maximal ideal $\mathfrak m$, and let $Q(B)$ denote the localisation of $B$ at its multiplicative set of non-zero-divisors, i.e. its total ring of fractions. Let $R$ be a $B$-subalgebra of $Q(B)$ which is finite as a $B$-module. Assume two things. First, for every prime ideal $\mathfrak q$ of $B$ with $\mathfrak q \ne \mathfrak m$ and every $r \in R$ there is an $s \in B$ with $s \notin \mathfrak q$ such that the image of $s$ in $Q(B)$ times $r$ lies in the range of the structure map $B \to Q(B)$; that is, every element of $R$ becomes an element of $B$ after multiplication by some element of $B$ outside $\mathfrak q$. Second, there exist $a, b \in \mathfrak m$ such that the two-term sequence $[a,b]$ is a regular sequence on $B$ in the sense of `RingTheory.Sequence.IsRegular`. The conclusion is that $R = \bot$, i.e. $R$ is the image of $B$ in $Q(B)$.
--
--   This is a depth-two recognition criterion of the type "a ring with a length-two regular sequence in its maximal ideal is determined by its localisations at the non-maximal primes": a module-finite overring inside the total ring of fractions which agrees with $B$ away from the closed point is already $B$. It is used in [`IsLocalRing.isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing`](thm.html#IsLocalRing.isDomain_and_isIntegrallyClosed_and_isFractionRing_of_forall_not_isMaximal_isRegularLocalRing), where a local ring all of whose non-maximal localisations are regular is shown to be a normal domain with the expected fraction field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Subalgebra_eq_bot_of_moduleFinite_of_forall_ne_maximalIdeal_of_isRegular_pair.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Subalgebra.eq_bot_of_moduleFinite_of_forall_ne_maximalIdeal_of_isRegular_pair
    {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (R : Subalgebra B (Localization (nonZeroDivisors B))) [Module.Finite B ↥R]
    (ha : ∀ (𝔮 : Ideal B) [𝔮.IsPrime], 𝔮 ≠ IsLocalRing.maximalIdeal B →
      ∀ r ∈ R, ∃ s : B, s ∉ 𝔮 ∧ (algebraMap B (Localization (nonZeroDivisors B)) s) * r ∈
        (algebraMap B (Localization (nonZeroDivisors B))).range)
    (hb : ∃ a b : B, a ∈ IsLocalRing.maximalIdeal B ∧ b ∈ IsLocalRing.maximalIdeal B ∧
      RingTheory.Sequence.IsRegular B [a, b]) :
    R = ⊥ := by sorry
