-- Prove2me | Theorems.Thm_PhilipponMultiplicity_section_five_contact_cosets
-- name    : PhilipponMultiplicity.section_five_contact_cosets
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-28T19:30:06.855086+00:00
-- url     : https://prove2.me/theorems/8f51f046-4107-4001-9be9-7017e40f6866
-- title:
--   Section 5 — finite contact cosets and sampling count
-- statement:
--   Use the original Section 5 construction, with selected maximal component $V$, chosen ideal $I_r$, contact order $T$, and sampling set $\Sigma$. Put
--
--   $$J=\sum_{v\in V}\tau_v(I_r),\qquad H_V(T)=Z_G(\mathcal D_{0,T}J).$$
--
--   The identity component $H=\operatorname{Stab}_G(V)^0$ is a connected algebraic subgroup. There is a finite set $R\subseteq H_V(T)$ such that
--
--   $$H_V(T)=\coprod_{g\in R}(g+H),\qquad \#((\Sigma+H)/H)\leq |R|.$$
--
--   The union is disjoint. Its members are actual cosets in the given algebraic group, and the locus is defined by the actual intrinsic differential ideal. This is the finite family and sampling lower bound used in the proof of Lemma 5.1.
-- source:
--   Patrice Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), proof of Lemma 5.1, printed pp. 381–382. https://numdam.org/articles/10.24033/bsmf.2060/ Finite coset decomposition and the inequality (***) on p. 381, refined to identity-component cosets on p. 382.

import Definitions.Def_PhilipponMultiplicity_SectionFive
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem section_five_contact_cosets
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveConstruction G A) :
    ∃ H : AlgebraicSubgroup G,
      H.carrier = C.stabilizer.identityComponent ∧ H.IsConnected ∧
      ∃ R : Finset G.Point,
        (∀ g ∈ R, g ∈ idealZeroLocusOnGroup G (differentialIdeal A 0 C.contactParameter
          (⨆ v : C.component, translatedIdeal G v.val C.chosenIdeal))) ∧
        idealZeroLocusOnGroup G (differentialIdeal A 0 C.contactParameter
          (⨆ v : C.component, translatedIdeal G v.val C.chosenIdeal)) =
            ⋃ g ∈ R, translate g H.carrier ∧
        (R : Set G.Point).Pairwise (fun g h => Disjoint
          (translate g H.carrier) (translate h H.carrier)) ∧
        cosetCount C.samplingSet H.carrier ≤ R.card := by sorry

end PhilipponMultiplicity
