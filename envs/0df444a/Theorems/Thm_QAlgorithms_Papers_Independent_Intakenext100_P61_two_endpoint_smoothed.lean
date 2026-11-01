-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_two_endpoint_smoothed
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.two_endpoint_smoothed
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:15:00.974797+00:00
-- url     : https://prove2.me/theorems/3b8997f1-bfe7-4058-a05c-9c451f88aa2a
-- title:
--   Remark 11: robust lower bound with both endpoints smoothed
-- statement:
--   There is a universal composed infidelity $\eta(\varepsilon,\varepsilon_0)\in[0,1]$ tending to zero as both nonnegative errors tend to zero. Let $\phi,\psi$ be normalized finite-dimensional bipartite pure vectors, $0\le\varepsilon,\varepsilon_0<1$, and suppose a deterministic quantum protocol prepares $\psi$ from $\phi$ with squared fidelity at least $1-\varepsilon$ and cost $C$. Whenever $\eta(\varepsilon,\varepsilon_0)<1/4$, put $d=(4\eta(\varepsilon,\varepsilon_0))^{1/8}$. Then
--
--   $$2C\ge\Delta_d(\psi_A)-\Delta_{\varepsilon_0}(\phi_A)+\log_2(1-\varepsilon_0)+2\log_2(1-d).$$
--
--   The quantities $\Delta_e$ use joint spectral-subset smoothing. The initial correction accounts for normalizing the retained initial state. The universal function is chosen before all systems, states and protocols; no explicit composition law is attributed to the source.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 5, Remark 11: robust lower bound with both endpoints smoothed

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

/-- PDF p.5, Remark 11: there is a universal composed infidelity, tending to
zero jointly. Applying Theorem 8 after normalizing an optimal initial spectral
projection incurs +log(1-epsilon0). The source gives no explicit composition law.
This is a local small-error bound: eta<1/4 is required by Theorem 8's domain. -/
theorem two_endpoint_smoothed :
    ∃ eta : ℝ × ℝ → ℝ,
      (∀ e e0 : ℝ, 0 ≤ e → e ≤ 1 → 0 ≤ e0 → e0 ≤ 1 → 0 ≤ eta (e,e0) ∧ eta (e,e0) ≤ 1) ∧
      Filter.Tendsto eta
        (nhdsWithin (0,0) {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) (nhds 0) ∧
      ∀ (A B C D : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
        [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
        (phi : EuclideanSpace ℂ (A × B)) (psi : EuclideanSpace ℂ (C × D)),
        ‖phi‖ = 1 → ‖psi‖ = 1 → ∀ (epsilon epsilon0 cost : ℝ),
        0 ≤ epsilon → epsilon < 1 → 0 ≤ epsilon0 → epsilon0 < 1 →
        eta (epsilon,epsilon0) < 1 / 4 → QuantumPrepares phi psi epsilon cost →
        2 * cost ≥ smoothSpread (aliceDensity psi) (smoothingError (eta (epsilon,epsilon0))) -
          smoothSpread (aliceDensity phi) epsilon0 + logTwo (1 - epsilon0) +
          2 * logTwo (1 - smoothingError (eta (epsilon,epsilon0))) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
