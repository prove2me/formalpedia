-- Prove2me | Theorems.Thm_PhilipponMultiplicity_section_five_counting_inequality
-- name    : PhilipponMultiplicity.section_five_counting_inequality
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-28T17:09:08.93444+00:00
-- url     : https://prove2.me/theorems/d8259330-3ef5-4705-bc15-a79bfaf1de88
-- title:
--   Lemma 5.1, second assertion — stabilizer coset and degree bound
-- statement:
--   Under the original Section 5 construction over either of Philippon's base fields, let $H$ be the identity component of the stabilizer of the selected common maximal component, and let $s=\operatorname{codim}_A(A\cap H)$. For the sampling set $\Sigma$, contact parameter $T$, polynomial multidegree $D$, and supplied positive translation bounds $c$,
--
--   $$\binom{T+s}{s}\,\#((\Sigma+H)/H)\,\mathcal H(H;D)\leq\mathcal H(G;cD).$$
--
--   The degree forms are obtained from the actual multigraded Hilbert polynomials; the coset count uses the actual subgroup carrier. This is precisely the second assertion of Lemma 5.1, with no additional multiplicity, smoothness, or counting certificate as a hypothesis.
-- source:
--   P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, BSMF 114 (1986), pp. 380–383, Lemma 5.1. https://www.numdam.org/item/BSMF_1986__114__355_0/

import Definitions.Def_PhilipponMultiplicity_SectionFive
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem section_five_counting_inequality
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (C : SectionFiveConstruction G A) :
    let H := C.stabilizer.identityComponent
      let s := analyticCodimension A H
      (Nat.choose (C.contactParameter + s) s : ℝ) *
          (cosetCount C.samplingSet H : ℝ) * hilbertDegreeForm G H C.degrees ≤
        hilbertDegreeForm G Set.univ C.scaledDegrees := by sorry

end PhilipponMultiplicity
