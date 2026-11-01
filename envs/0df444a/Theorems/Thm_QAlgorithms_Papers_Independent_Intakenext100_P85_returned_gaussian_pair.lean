-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P85_returned_gaussian_pair
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P85.returned_gaussian_pair
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:16:34.835851+00:00
-- url     : https://prove2.me/theorems/8cb16f40-633b-4e3d-8dd8-56b0be16f0df
-- title:
--   Eqs.(3)–(4): actual target-absent and target-present return–idler states
-- statement:
--   Let $N_S,N_B\ge0$ and $0<\kappa<1$. Prepare the SPDC number state above, transmit the signal, and retain the idler perfectly. Under $H_0$ replace the signal with an independent thermal mode of mean $N_B$. Under $H_1$ apply the thermal beam splitter $a_R=\sqrt\kappa a_S+\sqrt{1-\kappa}a_B$, with independent bath mean $N_B/(1-\kappa)$. The actual returned pairs are normalized zero-mean Gaussian densities with
--   $$
--   \Lambda_{RI}^{(0)}=\frac14\operatorname{diag}(B,B,S,S),\qquad
--   \Lambda_{RI}^{(1)}=\frac14\begin{pmatrix}A&0&\sqrt\kappa C_q&0\\0&A&0&-\sqrt\kappa C_q\\\sqrt\kappa C_q&0&S&0\\0&-\sqrt\kappa C_q&0&S\end{pmatrix},
--   $$
--   where $S=2N_S+1$, $C_q=2\sqrt{N_S(N_S+1)}$, $B=2N_B+1$, and $A=2\kappa N_S+B$. The covariance uses $(q_R,p_R,q_I,p_I)$ and vacuum variance $1/4$. This supplies the physical hypothesis pair, with bounded realizations of every channel slice included as conclusions.
-- source:
--   Quantum Illumination with Gaussian States, arXiv:0810.0534v1, PDF p. 2, Eqs.(3)–(4): actual target-absent and target-present return–idler states

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P85

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P85

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Renew46.P41 (coherentProductCoefficient)

/-- Source p.2, Eqs.(3)–(4): actual outputs of replacement/thermal-loss
on the constructed SPDC pair, with idler untouched. Gaussianity and the
covariance identities are conclusions, not channel/input assumptions. -/
theorem returned_gaussian_pair (k NS NB : ℝ) (hk : 0 < k) (hk1 : k < 1)
    (hNS : 0 ≤ NS) (hNB : 0 ≤ NB) (W : G.FockWeylSystem 2) :
    ∀ present : Bool,
      TargetRealized 1 present k NB (onePair (spdcArray NS)) ∧
      T.IsDensity (qiReturn present k NS NB) ∧
      SourceGaussian W (qiReturn present k NS NB) 0 (returnCov present k NS NB) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P85

end
