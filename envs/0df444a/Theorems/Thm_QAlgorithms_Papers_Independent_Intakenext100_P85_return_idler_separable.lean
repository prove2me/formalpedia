-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P85_return_idler_separable
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P85.return_idler_separable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:18:11.788259+00:00
-- url     : https://prove2.me/theorems/c544012f-b01d-4075-b9f4-acd0e7380e38
-- title:
--   pp.2,4: returned SPDC pair is classical and separable in bright noise
-- statement:
--   Let $N_S\ge0$, $0<\kappa<1$, and $N_B\ge\kappa$. Use the actual SPDC return–idler states of the thermal-loss/replacement experiment, with bath mean $N_B/(1-\kappa)$ under target presence and perfectly retained idler. Under both hypotheses,
--   $$
--   \rho_{RI}^{(h)}\text{ has a positive P representation and is separable across }R:I,\qquad h\in\{0,1\}.
--   $$
--   A positive P representation is a coherent-projector mixture under a Borel probability measure; singular measures are allowed at $N_B=\kappa$. Separability is the trace-norm closed convex hull of product densities on the complete oscillator spaces. This is a statement about the returned SPDC pair, not every channel input.
--
--   **Formalization Note** The p.4 phrase naming signal and return is corrected to return and idler, consistently with p.2, the covariance matrices and the abstract; independent moderation is required.
-- source:
--   Quantum Illumination with Gaussian States, arXiv:0810.0534v1, PDF p. 2, pp.2,4: returned SPDC pair is classical and separable in bright noise

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P85

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P85

open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov)

open QAlgorithms.Papers.Independent.Renew46.P41 (coherentProductCoefficient)

/-- Source p.2 and p.4: the actual return/idler pair is positive-P and
separable when NB>=k. Printed p.4 says S_m,R_m; changed to R_m,I_m
because p.2, (3)–(4) and the abstract specify this pair. Singular positive
measures are allowed at equality. This correction requires independent review. -/
theorem return_idler_separable (k NS NB : ℝ) (hk : 0 < k) (hk1 : k < 1)
    (hNS : 0 ≤ NS) (hNB : k ≤ NB) :
    ∀ present : Bool,
      PositiveP (qiReturn present k NS NB) ∧
      T.IsSeparable (pairArray (qiReturn present k NS NB)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P85

end
