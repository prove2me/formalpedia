-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P17_butterflyReduction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P17.butterflyReduction
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T13:51:04.43269+00:00
-- url     : https://prove2.me/theorems/2c5c993b-4900-461d-9577-99f868d42c2e
-- title:
--   Three computation-code uses in the butterfly network
-- statement:
--   Let $M_1,M_2\in F^\ell$ be independent uniform messages over a finite field. At $v_3$, decode their sum as $U$. Let $T_5,T_6$ be the forwarded copies of $U$ and let $S_1,S_2$ be the delivered side messages $-M_1,-M_2$. The computation receivers at $v_5,v_6$ decode $T_5+S_1,T_6+S_2$ as $V_5,V_6$. If all three computations and four deliveries are correct, then
--
--   $$
--   V_5=(M_1+M_2)+(-M_1)=M_2,\qquad
--   V_6=(M_1+M_2)+(-M_2)=M_1.
--   $$
--
--   The probability that either terminal is wrong is at most the sum of the seven corresponding error probabilities: the computation at $v_3$, the two central deliveries, the two negative side deliveries, and the computations at $v_5,v_6$. This gives the stated three-use coding reduction with sufficient link reliability, without assuming characteristic two or assigning an unspecified network capacity.
-- source:
--   Computation-aided classical-quantum multiple access to boost network communication speeds, arXiv:2105.14505v1, PDF p. 10, Appendix A and Figure 5

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P17

noncomputable section

open MeasureTheory

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Dependency50.P17

open QAlgorithms.Papers.Independent.Information100.P56 (productOutput)

/-- PDF pp.10–11, Appendix A and Figure 5: three COMP invocations, at v3,v5,v6.
u is v3's decoded sum, t5,t6 its forwarded copies, and s1,s2 the negative side
messages used at v5,v6. Outputs v5 and v6 recover b and a. The seven error events
include all three COMP decoders and the forwarding/side links. The signs follow
the displayed reconstruction equations in Figure 5; characteristic two is not assumed. -/
theorem butterflyReduction {F Omega : Type*} [Field F] [Fintype F]
    [MeasurableSpace F] [MeasurableSingletonClass F] [MeasurableSpace Omega]
    {ell : ℕ} (mu : Measure Omega) [IsProbabilityMeasure mu]
    (a b u t5 t6 s1 s2 v5 v6 : Omega → (Fin ell → F))
    (ha : Measurable a) (hb : Measurable b) (hu : Measurable u)
    (ht5 : Measurable t5) (ht6 : Measurable t6)
    (hs1 : Measurable s1) (hs2 : Measurable s2)
    (hv5 : Measurable v5) (hv6 : Measurable v6)
    (hmsg : UniformMessagePair mu a b) :
    (∀ w, u w = a w + b w → t5 w = u w → t6 w = u w →
      s1 w = -a w → s2 w = -b w →
      v5 w = t5 w + s1 w → v6 w = t6 w + s2 w →
      v5 w = b w ∧ v6 w = a w) ∧
    mu {w | v5 w ≠ b w ∨ v6 w ≠ a w} ≤
      mu {w | u w ≠ a w + b w} + mu {w | t5 w ≠ u w} + mu {w | t6 w ≠ u w} +
        mu {w | s1 w ≠ -a w} + mu {w | s2 w ≠ -b w} +
        mu {w | v5 w ≠ t5 w + s1 w} + mu {w | v6 w ≠ t6 w + s2 w}
    := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P17

end
