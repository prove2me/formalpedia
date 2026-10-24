-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P03_pure_mode_endpoint_limits
-- name    : QAlgorithms.Papers.Independent.Support50.P03.pure_mode_endpoint_limits
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T18:23:09.861675+00:00
-- url     : https://prove2.me/theorems/d1e93ba1-6849-4c2f-941a-edff76b5867b
-- title:
--   Vanishing grouped products at a pure symplectic mode
-- statement:
--   For $\lambda>1/2$, define $a(\lambda)=\tfrac12\ln((2\lambda+1)/(2\lambda-1))$ and
--
--   $$
--   f_1(\lambda)=a(\lambda)^2((2\lambda)^2-1),\qquad
--   f_2(\lambda)=a(\lambda)((2\lambda)^2-1).
--   $$
--
--   Both products have a zero continuous extension at the pure-mode endpoint:
--
--   $$
--   \lim_{\lambda\downarrow1/2} f_1(\lambda)=\lim_{\lambda\downarrow1/2} f_2(\lambda)=0,\qquad f_1(1/2)=f_2(1/2)=0.
--   $$
--
--   This identifies the finite grouped factors used in the variance formula when the first Gaussian state has pure modes; it does not assign a finite value to the divergent factor $a(1/2)$.
-- source:
--   Gaussian hypothesis testing and quantum illumination, arXiv:1608.06991v2, PDF p. 11, Appendix D, (D2) and following sentence

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P03

noncomputable section

open Filter

open scoped BigOperators ComplexOrder Topology Matrix

namespace QAlgorithms.Papers.Independent.Support50.P03

open QAlgorithms.Papers.Independent.Dependency50.P10
  (Phase complexify sigma thermalCovariance)

open QAlgorithms.Papers.Independent.Frontier30.P02 (PhaseMatrix)

/-- Equation (D2) and the following sentence, arXiv:1608.06991v2, PDF pp.10--11.
Both limits approach 1/2 FROM ABOVE; the products, rather than the divergent
arcoth factors individually, have the zero continuous extension. -/
theorem pure_mode_endpoint_limits :
    Tendsto pureModeF1 (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds 0) ∧
    Tendsto pureModeF2 (nhdsWithin (1 / 2 : ℝ) (Set.Ioi (1 / 2))) (nhds 0) ∧
    pureModeF1 (1 / 2) = 0 ∧ pureModeF2 (1 / 2) = 0 := by sorry

end QAlgorithms.Papers.Independent.Support50.P03

end
