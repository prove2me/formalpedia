-- Prove2me | Theorems.Thm_TranscendenceTheory_minimal_prime_primary_component
-- name    : TranscendenceTheory.minimal_prime_primary_component
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T18:44:42.493986+00:00
-- url     : https://prove2.me/theorems/b4fd3d49-3034-4f27-90a7-c64cb3a21a44
-- title:
--   Canonical primary component and finite multiplicity at a minimal prime
-- statement:
--   Let $R$ be a commutative Noetherian $\mathbb Q$-algebra, let $D:R\to R$ be a $\mathbb Q$-linear derivation, let $I$ be an ideal, and let $\mathfrak p$ be a minimal prime over $I$. Write $S=R_{\mathfrak p}$ and let $\iota:R\to S$ be the localization map.
--
--   There is a canonical primary ideal
--
--   $$
--   J=\iota^{-1}(IS)
--   $$
--
--   with all of the following properties:
--
--   1. $I\subseteq J$, the ideal $J$ is primary, and $\sqrt J=\mathfrak p$.
--   2. Its localization equals that of the original ideal:
--
--   $$
--   JS=IS.
--   $$
--
--   3. There exists a residual ideal $K\not\subseteq\mathfrak p$ such that
--
--   $$
--   I=J\cap K.
--   $$
--
--   4. There is a single separator $s\notin\mathfrak p$ with $sJ\subseteq I$.
--   5. The local quotient has finite module length:
--
--   $$
--   \operatorname{length}_S(S/IS)<\infty.
--   $$
--
--   6. For every nonnegative integer $T$, finite-order derivative containment is preserved:
--
--   $$
--   \left(\forall f\in I,\ \forall k\le T,\ D^k f\in\mathfrak p\right)
--   \quad\Longleftrightarrow\quad
--   \left(\forall f\in J,\ \forall k\le T,\ D^k f\in\mathfrak p\right).
--   $$
--
--   This constructs the isolated primary component used at the start of [Philippon (1986), Proposition 4.7, pp. 378–379](https://www.numdam.org/item/10.24033/bsmf.2060.pdf), once the minimal prime is known. Finiteness of the local multiplicity is the standard fact in [Stacks Project, Lemmas 10.62.3 and 10.62.5](https://stacks.math.columbia.edu/tag/00KY). No primary decomposition is supplied as a hypothesis. The theorem gives no numerical upper bound for the length and does not choose the geometric prime required by the zero estimate.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, Proposition 4.7, especially p. 379, and section 5, Lemma 5.1, pp. 380-382. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Stacks Project, Lemmas 10.62.3 and 10.62.5, https://stacks.math.columbia.edu/tag/00KY. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. Algebraic auxiliary theorem: construct the canonical primary component at a minimal prime in a Noetherian ring and prove finite local length and preservation of finite-order derivative containment. Geometric prime selection, transversality, and the total local-length degree budget remain open.

import Definitions.Def_TranscendenceTheory_MinimalPrimeMultiplicityData
import Mathlib.RingTheory.Localization.Ideal

theorem TranscendenceTheory.minimal_prime_primary_component
    (R : Type*) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
    (D : Derivation ℚ R R) (I p : Ideal R) [p.IsPrime]
    (hp : p ∈ I.minimalPrimes) :
    ∃ J : Ideal R,
      J = (I.map (algebraMap R (Localization.AtPrime p))).under R ∧
      I ≤ J ∧ J.IsPrimary ∧ J.radical = p ∧
      J.map (algebraMap R (Localization.AtPrime p)) =
        I.map (algebraMap R (Localization.AtPrime p)) ∧
      (∃ K : Ideal R, ¬ K ≤ p ∧ I = J ⊓ K) ∧
      (∃ s : R, s ∉ p ∧ ∀ f ∈ J, s * f ∈ I) ∧
      Module.length (Localization.AtPrime p)
        ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≠ ⊤ ∧
      ∀ T : ℕ,
        (∀ f ∈ I, ∀ k ≤ T, (D^[k]) f ∈ p) ↔
        (∀ f ∈ J, ∀ k ≤ T, (D^[k]) f ∈ p) := by sorry
