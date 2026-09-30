-- Prove2me | Theorems.Thm_PhilipponMultiplicity_section_five_finite_coset_degree_bound
-- name    : PhilipponMultiplicity.section_five_finite_coset_degree_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-28T19:30:05.276419+00:00
-- url     : https://prove2.me/theorems/f031e749-6cc9-4743-8752-0cba17e84c5a
-- title:
--   Section 5 — global degree bound for isolated cosets
-- statement:
--   Under the original Section 5 construction, let $H=\operatorname{Stab}_G(V)^0$ be its connected identity subgroup and let
--
--   $$J=\sum_{v\in V}\tau_v(I_r).$$
--
--   Let $R$ be any finite set whose cosets $g+H$ are pairwise disjoint. Suppose $J$ incompletely defines each of those cosets with multiplicity at least the natural number $\ell$. Then
--
--   $$\ell\,|R|\,\mathcal H(H;D)\leq \mathcal H(G;cD).$$
--
--   Here $D$ is the original polynomial multidegree and $c$ is the supplied bound on the translation chart degrees. The forms are the actual multigraded Hilbert degree forms, and all local lengths are canonical. This isolates the global degree estimate in the last part of the proof of Lemma 5.1, allowing any common multiplicity lower bound. Zero values of $\ell$ and entries of $D$ are included; no positivity assumption on $D$ is added.
-- source:
--   Patrice Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), proof of Lemma 5.1, printed pp. 381–382. https://numdam.org/articles/10.24033/bsmf.2060/ The final three displayed degree estimates on p. 382, after replacing J by its bounded polynomial-operator ideal J′, applying Proposition 3.3 and Lemma 4.5. The common multiplicity lower bound is denoted ell here; the source uses binomial(T+s,s).

import Definitions.Def_PhilipponMultiplicity_SectionFive
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem section_five_finite_coset_degree_bound
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveConstruction G A)
    (H : AlgebraicSubgroup G) (hH : H.carrier = C.stabilizer.identityComponent)
    (hconn : H.IsConnected) (R : Finset G.Point) (ell : ℕ)
    (hdisjoint : (R : Set G.Point).Pairwise (fun g h => Disjoint
      (translate g H.carrier) (translate h H.carrier)))
    (hmultiplicity : ∀ g ∈ R, IncompletelyDefinesWithMultiplicityAtLeast G
      (⨆ v : C.component, translatedIdeal G v.val C.chosenIdeal) (translate g H.carrier) ell) :
    (ell : ℝ) * (R.card : ℝ) * hilbertDegreeForm G H.carrier C.degrees ≤
      hilbertDegreeForm G Set.univ C.scaledDegrees := by sorry

end PhilipponMultiplicity
