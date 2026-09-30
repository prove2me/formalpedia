-- Prove2me | Theorems.Thm_TranscendenceTheory_isolated_component_differential_contact
-- name    : TranscendenceTheory.isolated_component_differential_contact
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-20T17:32:00.646988+00:00
-- url     : https://prove2.me/theorems/44e5bbc6-ff76-4d1a-8f26-0f12dd9905b5
-- title:
--   Isolating an ideal component preserves local multiplicity and differential contact
-- statement:
--   Let $R$ be a commutative $\mathbb Q$-algebra, let $D:R\to R$ be a $\mathbb Q$-linear derivation, and let $\mathfrak p$ be a prime ideal. Let $J_0,\ldots,J_{r-1}$ be a finite family of ideals, with a distinguished index $i<r$, and suppose
--
--   $$
--   J_j\not\subseteq\mathfrak p\qquad(j\ne i).
--   $$
--
--   Write $I=\bigcap_{j<r}J_j$, let $S=R_{\mathfrak p}$, and write $KS$ for the extension of an ideal $K$ to $S$.
--
--   There exists an element $s\notin\mathfrak p$ with the following properties:
--
--   1. $sJ_i\subseteq I$.
--   2. The localized ideals agree:
--
--   $$
--   IS=J_iS.
--   $$
--
--   3. For every integer $T\ge0$, derivative containment transfers exactly:
--
--   $$
--   \left(\forall f\in I,\ \forall k\le T,\ D^k f\in\mathfrak p\right)
--   \quad\Longleftrightarrow\quad
--   \left(\forall f\in J_i,\ \forall k\le T,\ D^k f\in\mathfrak p\right).
--   $$
--
--   4. If $J_i$ is primary and $\sqrt{J_i}=\mathfrak p$, then the contraction of $IS$ to $R$ is exactly $J_i$:
--
--   $$
--   \iota^{-1}(IS)=J_i,\qquad \iota:R\longrightarrow S.
--   $$
--
--   The equality of localized ideals identifies their quotient modules and therefore preserves local multiplicity. The theorem applies to the isolated primary component used in the opening of [Philippon (1986), Proposition 4.7, p. 379](https://www.numdam.org/item/10.24033/bsmf.2060.pdf). Its first three assertions require only the stated separation condition; primaryness is needed only for the final contraction assertion. The theorem does not assert the existence of a suitable geometric family or a bound on its total multiplicity.
-- source:
--   Philippon (1986), Lemmes de zeros dans les groupes algebriques commutatifs, Bull. Soc. Math. France 114, 355-383, Proposition 4.7, especially p. 379, and section 5, Lemma 5.1, pp. 380-382. https://www.numdam.org/item/10.24033/bsmf.2060.pdf. Senthil Kumar K (2026), Appendix A, Theorem A.2. https://doi.org/10.1017/S001309152610145X. Algebraic auxiliary theorem: isolate an ideal component with a separator outside the prime and prove preservation of the local quotient and finite-order derivative containment. Component selection, global transversality, and the total local-length degree budget remain open.

import Definitions.Def_TranscendenceTheory_PrimeMultiplicityData
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Ideal.IsPrimary

theorem TranscendenceTheory.isolated_component_differential_contact
    (R : Type*) [CommRing R] [Algebra ℚ R]
    (D : Derivation ℚ R R) (p : Ideal R) [p.IsPrime]
    (n : ℕ) (J : Fin n → Ideal R) (i : Fin n)
    (hother : ∀ j, j ≠ i → ¬ J j ≤ p) :
    ∃ s : R, s ∉ p ∧
      (∀ f ∈ J i, s * f ∈ ⨅ j, J j) ∧
      (⨅ j, J j).map (algebraMap R (Localization.AtPrime p)) =
        (J i).map (algebraMap R (Localization.AtPrime p)) ∧
      (∀ T : ℕ,
        (∀ f ∈ ⨅ j, J j, ∀ k ≤ T, (D^[k]) f ∈ p) ↔
        (∀ f ∈ J i, ∀ k ≤ T, (D^[k]) f ∈ p)) ∧
      ((J i).IsPrimary → (J i).radical = p →
        ((⨅ j, J j).map (algebraMap R (Localization.AtPrime p))).under R = J i) := by sorry
