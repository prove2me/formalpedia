-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_smooth_renyi_communication_lower
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.smooth_renyi_communication_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:15:40.224319+00:00
-- url     : https://prove2.me/theorems/ba9506fa-7fdb-4c1b-9415-fe18c1c67618
-- title:
--   Remark 12: smoothed Renyi-gap communication bound
-- statement:
--   Let $0\le\alpha<1<\beta\le\infty$ and let normalized bipartite pure states $\phi,\psi$ be related by a deterministic quantum protocol of cost $C$ and unconditional squared fidelity at least $1-\varepsilon$, with $0\le\varepsilon<1/4$. For eigenvalues $r_j$, define $\Delta_e^{\alpha\beta}$ by jointly minimizing $\log_2(\sum_{j\in J}r_j^\alpha)/(1-\alpha)-\log_2(\sum_{j\in J}r_j^\beta)/(1-\beta)$ over retained mass at least $1-e$. Order zero counts positive support; infinity uses the largest retained weight. Put $\delta=(4\varepsilon)^{1/8}$. Then
--
--   $$2C\ge\Delta_\delta^{\alpha\beta}(\psi_A)-\Delta_0^{\alpha\beta}(\phi_A)+\left(\frac{2\alpha}{1-\alpha}+\frac{2\beta}{\beta-1}\right)\log_2(1-\sqrt\delta).$$
--
--   The factor $\beta/(\beta-1)$ equals one at infinity. This retains the source's separate smoothing correction.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 5, Remark 12: smoothed Renyi-gap communication bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

section Operational

variable {A B C D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

/-- PDF p.5, Remark 12: jointly smoothed Renyi gaps, with the infinity limit
and the printed log(1-sqrt(delta)) correction. -/
theorem smooth_renyi_communication_lower (phi : EuclideanSpace ℂ (A × B))
    (psi : EuclideanSpace ℂ (C × D)) (hphi : ‖phi‖ = 1) (hpsi : ‖psi‖ = 1)
    (alpha : NNReal) (halpha : alpha < 1) (beta : RenyiOrder) (hbeta : 1 < beta)
    (epsilon cost : ℝ) (hzero : 0 ≤ epsilon) (hsmall : epsilon < 1 / 4)
    (hprotocol : QuantumPrepares phi psi epsilon cost) :
    2 * cost ≥ smoothRenyiGap (aliceDensity psi) (alpha : RenyiOrder) beta (smoothingError epsilon) -
      smoothRenyiGap (aliceDensity phi) (alpha : RenyiOrder) beta 0 +
      (2 * (alpha : ℝ) / (1 - (alpha : ℝ)) + 2 * upperRenyiFactor beta) *
        logTwo (1 - Real.sqrt (smoothingError epsilon)) := by sorry

end Operational

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
