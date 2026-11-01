-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_epr_assisted_lower
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.epr_assisted_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:13:34.921899+00:00
-- url     : https://prove2.me/theorems/be474783-a10e-46ec-b42c-36207a50d32f
-- title:
--   Corollary 9: arbitrary EPR assistance
-- statement:
--   Let $\phi,\psi$ be normalized bipartite pure states and let $k\ge0$ be any finite integer. A deterministic protocol starts with $\phi$ and $k$ additional EPR pairs and has unconditional output of squared fidelity at least $1-\varepsilon$ to $\psi$, where $0\le\varepsilon<1/4$. With quantum cost $C=\sum_i\log_2 d_i$, $\delta=(4\varepsilon)^{1/8}$ and joint spectral-subset smooth spread $\Delta_e$,
--
--   $$2C\ge\Delta_\delta(\psi_A)-\Delta(\phi_A)+2\log_2(1-\delta).$$
--
--   There is no upper bound on $k$, and the initial term is computed from $\phi$ alone. This permits finite EPR assistance without arbitrary catalysts.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 5, Corollary 9: arbitrary EPR assistance

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

/-- PDF p.5, Corollary 9: any finite number k of supplementary EPR pairs;
the right-hand side still uses phi alone. -/
theorem epr_assisted_lower (phi : EuclideanSpace ℂ (A × B))
    (psi : EuclideanSpace ℂ (C × D)) (hphi : ‖phi‖ = 1) (hpsi : ‖psi‖ = 1)
    (k : ℕ) (epsilon cost : ℝ) (hzero : 0 ≤ epsilon) (hsmall : epsilon < 1 / 4)
    (hprotocol : QuantumPrepares (tensorPureStates phi (eprPairs k)) psi epsilon cost) :
    2 * cost ≥ smoothSpread (aliceDensity psi) (smoothingError epsilon) -
      spread (aliceDensity phi) + 2 * logTwo (1 - smoothingError epsilon) := by sorry

end Operational

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
