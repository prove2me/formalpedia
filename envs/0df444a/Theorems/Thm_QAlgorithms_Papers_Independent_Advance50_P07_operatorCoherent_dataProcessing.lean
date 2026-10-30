-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_operatorCoherent_dataProcessing
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.operatorCoherent_dataProcessing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:38:15.935653+00:00
-- url     : https://prove2.me/theorems/d9595231-d35c-4f16-b586-b4d8b69f11de
-- title:
--   Data processing for operator-smoothed zero coherent information
-- statement:
--   Let $\rho^{AB}$ be a normalized bipartite state on nonzero finite-dimensional registers, let $\Phi:\mathcal B(B)\to\mathcal B(C)$ be CPTP with $C$ nonzero and finite-dimensional, and let $\delta\ge0$. Write $\widetilde I^c_{0,\delta}(\rho)=\max_{P\in p(\rho;\delta)}\min_{\sigma^B\in\mathcal S(B)}S_0^P(\rho\Vert1_A\otimes\sigma^B)$, where $p(\rho;\delta)=\{0\le P\le1:\operatorname{Tr}P\rho\ge1-\delta\}$ and $S_0^P(\rho\Vert\sigma)=-\log_2\operatorname{Tr}(\sqrt P\Pi_\rho\sqrt P\sigma)$. Then
--
--   $$\widetilde I^c_{0,\delta}((\operatorname{id}_A\otimes\Phi)(\rho))\le\widetilde I^c_{0,2\sqrt\delta}(\rho).$$
--
--   Both extrema in each smoothed quantity are attained. The quantities take extended real values, including $+\infty$ when a zero effect is admissible. This is the data-processing estimate used for the transmission converse.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 10, Lemma 12 (Quantum data-processing inequality)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P07

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology

open Filter

namespace QAlgorithms.Papers.Independent.Advance50.P07

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P09 (relativeD petzD)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative Density elog)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P19 (marginalRA marginalRB)

open QAlgorithms.Papers.Independent.Support50.P21 (PositiveTensorBasis)

/-- Lemma 12, PDF p.10. Radius is 2 sqrt(delta), for all delta>=0.
The extended extrema have attaining effects and comparison states. -/
theorem operatorCoherent_dataProcessing {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [Nonempty A] [Nonempty B] [Nonempty C]
    (rho : Mat (A × B)) (hrho : IsDensityMatrix rho)
    (Phi : Superop B C) (hPhi : IsChannel Phi) (delta : ℝ) (hdelta : 0 ≤ delta) :
    operatorCoherent (idTensorSuperop Phi rho) delta ≤ operatorCoherent rho (2 * Real.sqrt delta) ∧
    OperatorAttained rho (2 * Real.sqrt delta) ∧
    OperatorAttained (idTensorSuperop Phi rho) delta := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
