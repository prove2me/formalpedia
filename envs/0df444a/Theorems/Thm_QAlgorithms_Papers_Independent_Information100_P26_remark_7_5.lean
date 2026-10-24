-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_remark_7_5
-- name    : QAlgorithms.Papers.Independent.Information100.P26.remark_7_5
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:00:40.558985+00:00
-- url     : https://prove2.me/theorems/54845334-220a-4fa4-9446-d9ec79cd966e
-- title:
--   Remark 7.5: stationary-density primitivity and the generator kernel
-- statement:
--   Let $(\tau_t=e^{tL})_{t\ge0}$ be a continuous semigroup of unital CP, trace-preserving channels on $M_d$, $d\ge1$, with its actual generator. Then
--   $$ (\tau_t)_{t\ge0}\text{ is primitive}\quad\Longleftrightarrow\quad\ker L=\mathbb C I_d.$$
--   Primitivity is defined by the unique strictly positive stationary density matrix of the adjoint semigroup. This is a characterization, rather than a definition made from the conclusion.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 27, Remark 7.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Remark 7.5, PDF pp.27. -/
theorem remark_7_5 {d : ℕ} (hd : 0 < d) (s : ChannelSemigroup d) :
    SemigroupPrimitive s ↔ {X : Mat d | applyMap s.generator X = 0} = (scalars d : Set (Mat d)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
