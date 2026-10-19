-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P26_lemma_4_5
-- name    : QAlgorithms.Papers.Independent.Information100.P26.lemma_4_5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:26:58.290966+00:00
-- url     : https://prove2.me/theorems/7fff6e38-bdd4-41ac-a1fe-a6ed7d59f75c
-- title:
--   Lemma 4.5: weighted Haar average with depolarizing remainder
-- statement:
--   Let $d\ge2$ and let $\tau$ be a unital quantum channel. With $a_d=1/((d-1)(d+1)^2)$ and independent normalized Haar integration,
--   $$\int\!\int\operatorname{Re}\langle\beta_{U,V},\tau\rangle\,\beta_{U,V}\,dU\,dV=a_d\tau+(1-a_d)\delta_d.$$
--   The Hilbert–Schmidt inner product is conjugate-linear in its first argument and is real here. At $d=2$, the coefficients are $1/9$ and $8/9$. This is the weighted integral identity used in the affine representation.
-- source:
--   A complete characterization of eventually entanglement breaking unital quantum channels, arXiv:2609.24168v1, PDF p. 15, Lemma 4.5

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder Matrix.Norms.Frobenius

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P26

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] QAlgorithms.Papers.Independent.Information100.P26.unitaryMeasurable

/-- arXiv:2609.24168v1, Lemma 4.5, PDF pp.15,16. -/
theorem lemma_4_5 {d : ℕ} (hd : 2 ≤ d) (mu : Measure (Unitary d))
    (hmu : NormalizedHaar mu) (t : Map d) (ht : UnitalChannel t) :
    weightedIntegral mu (fun U V => (hsInner (beta U V) t).re) =
      (integralDenominator d)⁻¹ • t +
        (1 - (integralDenominator d)⁻¹) • depolarizing d := by sorry

end QAlgorithms.Papers.Independent.Information100.P26

end
