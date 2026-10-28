-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_theorem_4_1
-- name    : QAlgorithms.Papers.Independent.Information100.P26.theorem_4_1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:25:08.658002+00:00
-- url     : https://prove2.me/theorems/124a0203-a490-48f8-bbcf-02ee68f67a6f
-- title:
--   Theorem 4.1: real-weighted Haar reconstruction of every unital channel
-- statement:
--   For $d\ge1$, let $\tau$ be a unital quantum channel on $M_d$. Put $D_d=(d-1)(d+1)^2$. With independent normalized Haar measures on $U(d)$,
--   $$\tau=\int\!\int\big[D_d\operatorname{Re}\langle\beta_{U,V},\tau\rangle-D_d+1\big]\beta_{U,V}\,dU\,dV.$$
--   Here $\beta_{U,V}=\operatorname{Ad}_U\Delta_d\operatorname{Ad}_{V^*}$ and $\langle\phi,\psi\rangle=\operatorname{Tr}(J(\phi)^*J(\psi))$. This inner product is real on CP maps; its reality is not assumed. For $d=1$ the weight is one.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 14, Theorem 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Theorem 4.1, PDF pp.14,16. -/
theorem theorem_4_1 {d : ℕ} (hd : 0 < d) (mu : Measure (Unitary d))
    (hmu : NormalizedHaar mu) (t : Map d) (ht : UnitalChannel t) :
    t = weightedIntegral mu (fun U V =>
      integralDenominator d * (hsInner (beta U V) t).re - integralDenominator d + 1) := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
