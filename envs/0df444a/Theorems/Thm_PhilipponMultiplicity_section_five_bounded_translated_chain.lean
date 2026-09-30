-- Prove2me | Theorems.Thm_PhilipponMultiplicity_section_five_bounded_translated_chain
-- name    : PhilipponMultiplicity.section_five_bounded_translated_chain
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-29T10:00:37.337769+00:00
-- url     : https://prove2.me/theorems/8ffcb352-6891-41c2-8406-61d343bc7a29
-- title:
--   Section 5 — bounded equations preserving translated-chain multiplicities
-- statement:
--   Let $K$ be a complete nontrivially normed field. Take the original Section 5 input, including the homogeneous polynomial $P$ of multidegree $D$ and polynomial translation atlases bounded by $c$. For every chain stage $I_n$ and every nonempty subset $V$ of the group, put $J=\sum_{v\in V}\tau_v(I_n)$. There is a homogeneous ideal $J'$ containing $I(G)$ and generated modulo $I(G)$ by finitely many homogeneous equations of multidegrees at most $cD$ such that $J'$ and $J$ have equal retained ideals and equal localizations at every genuine homogeneous representative of a group point.
--
--   For every subset $W$ and every natural number $\ell$, $J'$ incompletely defines $W$ with multiplicity at least $\ell$ if and only if $J$ does. Multiplicity is the actual localized quotient length. This is the bounded replacement on pp. 381–382, generalized from the selected component to any nonempty translating set. The chain stage zero, contact order zero, and zero entries in $D$ are included.
-- source:
--   Patrice Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), proof of Theorem 2.1 and Lemma 5.1, printed pp. 381–382. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionFive
import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem section_five_bounded_translated_chain
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveInput G A) (n : ℕ) (V : Set G.Point) (hV : V.Nonempty) :
    ∃ J' : Ideal G.CoordinateRing,
      G.vanishingIdeal Set.univ ≤ J' ∧ IsMultihomogeneousIdeal G.ambient J' ∧
      Hilbert.HasEquationsOfDegreeAtMost K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) J' C.scaledDegrees ∧
      retainOnGroup G J' = retainOnGroup G (⨆ v : V, translatedIdeal G v.val (C.idealChain n)) ∧
      (∀ x : GroupHomogeneousRepresentative G,
        J'.map (algebraMap G.CoordinateRing
          (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal)) =
        (⨆ v : V, translatedIdeal G v.val (C.idealChain n)).map
          (algebraMap G.CoordinateRing
            (Localization.AtPrime (representativeMaximalIdeal G x).asIdeal))) ∧
      (∀ W : Set G.Point, ∀ ell : ℕ,
        IncompletelyDefinesWithMultiplicityAtLeast G J' W ell ↔
        IncompletelyDefinesWithMultiplicityAtLeast G
          (⨆ v : V, translatedIdeal G v.val (C.idealChain n)) W ell) := by sorry

end PhilipponMultiplicity
