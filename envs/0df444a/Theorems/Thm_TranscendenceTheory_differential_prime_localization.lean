-- Prove2me | Theorems.Thm_TranscendenceTheory_differential_prime_localization
-- name    : TranscendenceTheory.differential_prime_localization
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T17:05:51.853008+00:00
-- url     : https://prove2.me/theorems/580f906d-5b56-4ab8-b527-c68a6f3cb541
-- title:
--   Derivations and finite-order contact under prime localization
-- statement:
--   Let $R$ be a commutative $\mathbb Q$-algebra, $D:R\to R$ a $\mathbb Q$-linear derivation, and $\mathfrak p\subset R$ a prime ideal. Put
--
--   $$
--   S=R_{\mathfrak p},\qquad\iota:R\to S,\qquad\mathfrak m=\mathfrak pR_{\mathfrak p}.
--   $$
--
--   There exists a $\mathbb Q$-linear derivation $d:S\to S$ such that
--
--   $$
--   d(\iota(a))=\iota(Da)\qquad(a\in R).
--   $$
--
--   For this same derivation, for every ideal $I\subseteq R$ and every integer $T\ge0$, the following conditions are equivalent:
--
--   $$
--   D^j f\in\mathfrak p\quad\text{for every }f\in I\text{ and }0\le j\le T;
--   $$
--
--   $$
--   d^j g\in\mathfrak m\quad\text{for every }g\in IS\text{ and }0\le j\le T.
--   $$
--
--   No domain, Noetherian, or finite-length hypothesis on $R$ is required. In particular, injectivity of the localization map is not assumed.
--
--   **Formalization Note.** This is the localization and derivative-containment step needed when applying the local multiplicity argument of [Philippon (1986), Proposition 4.7, especially the opening paragraph on p. 379](https://www.numdam.org/item/10.24033/bsmf.2060.pdf). It is a separate algebraic auxiliary theorem, not a claim to prove that entire proposition. The proof uses the localization base-change theorem for Kähler differentials from [Mathlib's étale Kähler differential module at the pinned revision](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RingTheory/Etale/Kaehler.lean).
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, Proposition 4.7, especially p. 379, and section 5, Lemma 5.1, pp. 380-382. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. Algebraic auxiliary theorem: construct the derivation on the prime localization and prove exact transfer of finite-order derivative containment. Component selection, global transversality, and the total local-length degree budget remain open.

import Definitions.Def_TranscendenceTheory_PrimeMultiplicityData

theorem TranscendenceTheory.differential_prime_localization
    (R : Type*) [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (p : Ideal R) [p.IsPrime] :
    ∃ d : Derivation ℚ (Localization.AtPrime p) (Localization.AtPrime p),
      (∀ a : R, d (algebraMap R (Localization.AtPrime p) a) =
        algebraMap R (Localization.AtPrime p) (D a)) ∧
      ∀ (I : Ideal R) (T : ℕ),
        (∀ f ∈ I, ∀ j ≤ T, (D^[j]) f ∈ p) ↔
        (∀ f ∈ I.map (algebraMap R (Localization.AtPrime p)), ∀ j ≤ T,
          (d^[j]) f ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p)) := by sorry
