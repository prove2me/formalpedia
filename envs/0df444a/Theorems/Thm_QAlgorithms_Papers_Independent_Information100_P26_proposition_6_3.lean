-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_proposition_6_3
-- name    : QAlgorithms.Papers.Independent.Information100.P26.proposition_6_3
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:44:00.793866+00:00
-- url     : https://prove2.me/theorems/64306843-0875-407d-bd61-f019e8ba51ed
-- title:
--   Proposition 6.3: reduction by the commutant of the peripheral center
-- statement:
--   For every unital quantum channel $\tau$ on $M_d$, $d\ge1$,
--   $$Z(\mathcal P(\tau))'\text{ reduces }\tau.$$
--   Here $\mathcal P(\tau)$ is the complex span of eigenvectors whose eigenvalues have modulus one; center and commutant use the ordinary matrix product. Reduction asserts invariance of this subspace and its Hilbert–Schmidt orthogonal complement. No commutativity of the peripheral space is assumed.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 22, Proposition 6.3

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Proposition 6.3, PDF pp.22. -/
theorem proposition_6_3 {d : ℕ} (hd : 0 < d) (t : Map d) (ht : UnitalChannel t) :
    Reduces t (commutant (center (peripheral t : Set (Mat d)))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
