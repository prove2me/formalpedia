-- Prove2me | Theorems.Thm_PhilipponMultiplicity_section_five_stabilizer_incomplete_definition
-- name    : PhilipponMultiplicity.section_five_stabilizer_incomplete_definition
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-28T17:09:20.910259+00:00
-- url     : https://prove2.me/theorems/9c194329-6f9a-4453-9645-bc423d57c171
-- title:
--   Lemma 5.1, third assertion — the translated ideal defines the stabilizer
-- statement:
--   Under the original Section 5 construction over either of Philippon's base fields, write $V$ for the selected common maximal component and $I_r$ for its chosen ideal. The ideal
--
--   $$J=\sum_{v\in V}\tau_v(I_r)$$
--
--   incompletely defines the actual stabilizer $\operatorname{Stab}_G(V)$. Translation means pullback by $x\mapsto v+x$. Incomplete definition has the original minimal-prime meaning: the stabilizer is its own group zero locus, and every minimal prime of its homogeneous vanishing ideal meeting $G$ is a minimal prime of $I(G)+J$. This is precisely the third assertion of Lemma 5.1; the conclusion is not assumed as part of the construction.
-- source:
--   P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, BSMF 114 (1986), pp. 380–383, Lemma 5.1. https://www.numdam.org/item/BSMF_1986__114__355_0/

import Definitions.Def_PhilipponMultiplicity_SectionFive
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem section_five_stabilizer_incomplete_definition
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveConstruction G A) :
    IncompletelyDefines G
      (⨆ v : {x : G.Point // x ∈ C.component}, translatedIdeal G v.1 C.chosenIdeal)
      C.stabilizer.carrier := by sorry

end PhilipponMultiplicity
