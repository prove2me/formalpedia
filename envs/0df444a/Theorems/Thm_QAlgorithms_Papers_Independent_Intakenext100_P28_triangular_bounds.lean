-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_triangular_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.triangular_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:29:03.012905+00:00
-- url     : https://prove2.me/theorems/be6b2b0a-27a3-4ab3-8958-9d44ec6b71bc
-- title:
--   Theorem 3: Triangular discrimination satisfies Delta log e<=c1 D; Delta log e<=D+c2 TV log e; Delta log e<=(Dforward+Dreverse)/2
-- statement:
--   Let $\Delta$ be triangular discrimination and $\ell=\log_b e$. Uniformly over probability pairs $P\ll Q$,
--
--   $$\Delta(P\|Q)\ell\le c_1D(P\|Q),\qquad
--   \Delta(P\|Q)\ell\le D(P\|Q)+c_2|P-Q|\ell.$$
--
--   Here $c_1=\sup_{t>0,t\ne1}[(t-1)^2\ell/((t+1)r(t))]$ and $c_2$ is the least nonnegative $c$ for which $(t-1)^2\ell/(t+1)\le r(t)+2c(1-t)\ell$ for every $0<t<1$, with $r(t)=t\log_b t+(1-t)\ell$. Both constants are best possible. For mutually absolutely continuous pairs, $\Delta\ell\le[D(P\|Q)+D(Q\|P)]/2$ with best coefficient $1/2$. Rounded decimals in the paper are not used as exact constants.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 18, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 3: Triangular discrimination satisfies Delta log e<=c1 D; Delta log e<=D+c2 TV log e; Delta log e<=(Dforward+Dreverse)/2. Sason--Verdu, arXiv:1508.00335v7, PDF p.18.  -/
theorem triangular_bounds
    (b : LogBase) :
    Sharp (fun P Q => triangular P Q * ENNReal.ofReal (logBaseE b)) (kl b)
      acPairs (triangularC1 b) ∧
    IsLeast {c | ∀ (A : Type u) [MeasurableSpace A] (P Q : Measure A)
      [IsProbabilityMeasure P] [IsProbabilityMeasure Q], P ≪ Q →
        triangular P Q * ENNReal.ofReal (logBaseE b) ≤ kl b P Q + c * fullVariation P Q * ENNReal.ofReal (logBaseE b)}
      (triangularC2 b) ∧
    Sharp (fun P Q => triangular P Q * ENNReal.ofReal (logBaseE b))
      (symmetricKL b) mutualPairs (1 / 2) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
