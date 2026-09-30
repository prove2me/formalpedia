-- Prove2me | Theorems.Thm_PhilipponMultiplicity_section_five_contact_coset_multiplicity
-- name    : PhilipponMultiplicity.section_five_contact_coset_multiplicity
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-28T19:29:37.355594+00:00
-- url     : https://prove2.me/theorems/4c068093-c19f-423f-8511-dd1b74a95ef8
-- title:
--   Section 5 — binomial multiplicities of contact cosets
-- statement:
--   Under the original Section 5 construction, let $H=\operatorname{Stab}_G(V)^0$, represented as a connected algebraic subgroup, and put
--
--   $$J=\sum_{v\in V}\tau_v(I_r),\qquad s=\operatorname{codim}_A(A\cap H).$$
--
--   For every point $g\in Z_G(\mathcal D_{0,T}J)$, the ideal $J$ incompletely defines $g+H$ with multiplicity at least
--
--   $$\binom{T+s}{s}.$$
--
--   Incomplete definition means isolation of the actual minimal primes, and the multiplicity is the canonical localized quotient length. Neither isolation in $Z_G(J)$ nor isolation in $Z_G(\mathcal D_{0,T}J)$ is assumed: both are conclusions needed to apply Proposition 4.7.
-- source:
--   Patrice Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), proof of Lemma 5.1, printed pp. 381–382. https://numdam.org/articles/10.24033/bsmf.2060/ The first paragraph of p. 382 applies Proposition 4.7 to cosets isolated at both orders zero and T.

import Definitions.Def_PhilipponMultiplicity_SectionFive
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem section_five_contact_coset_multiplicity
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveConstruction G A)
    (H : AlgebraicSubgroup G) (hH : H.carrier = C.stabilizer.identityComponent)
    (hconn : H.IsConnected) (g : G.Point)
    (hg : g ∈ idealZeroLocusOnGroup G (differentialIdeal A 0 C.contactParameter
      (⨆ v : C.component, translatedIdeal G v.val C.chosenIdeal))) :
    IncompletelyDefinesWithMultiplicityAtLeast G
      (⨆ v : C.component, translatedIdeal G v.val C.chosenIdeal) (translate g H.carrier)
      (Nat.choose (C.contactParameter + analyticCodimension A H.carrier)
        (analyticCodimension A H.carrier)) := by sorry

end PhilipponMultiplicity
