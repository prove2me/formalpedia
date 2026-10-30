-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P07_operatorCoherent_le_coherent
-- name    : QAlgorithms.Papers.Independent.Advance50.P07.operatorCoherent_le_coherent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:40:16.915025+00:00
-- url     : https://prove2.me/theorems/76d8495c-d8ae-4560-899e-79de6850615e
-- title:
--   Comparison with ordinary coherent information
-- statement:
--   Let $\rho^{AB}$ be a density operator on nonzero finite-dimensional registers of dimensions $d_A,d_B$. Let $0\le\delta<1/4$, put $\delta'=2\sqrt\delta$, and use $I^c(\rho)=S(\rho^B)-S(\rho^{AB})$. With the operator-smoothed zero coherent information of (12),
--
--   $$\widetilde I^c_{0,\delta}(\rho^{AB})\le\frac{I^c(\rho^{AB})}{1-\delta'}+\frac{4(\delta'\log_2(d_Ad_B)+1)}{1-\delta'}.$$
--
--   The effect and comparison-state extrema are attained. This quantitative estimate links the one-shot converse quantity to ordinary coherent information.
--
--   **Source correction.** The printed $\delta\ge0$ domain is restricted to $\delta<1/4$, the division domain of (46)–(47). The numerator is transcribed with $\delta'$ as printed. Lemma 10 is not assumed.
-- source:
--   The quantum capacity of channels with arbitrarily correlated noise, arXiv:0902.0158v5, PDF p. 12, Lemma 14, operator-smoothed coherent information versus ordinary coherent information

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

/-- Lemma 14, PDF pp.12–13, (44). SOURCE CORRECTION: restrict printed
delta>=0 to 0<=delta<1/4, required by (46)–(47). Numerator uses
delta PRIME=2 sqrt(delta). No false Lemma 10 comparison is assumed. -/
theorem operatorCoherent_le_coherent {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Mat (A × B)) (hrho : IsDensityMatrix rho) (delta : ℝ)
    (hdelta : 0 ≤ delta) (hsmall : delta < 1/4) :
    operatorCoherent rho delta ≤
      ((stateCoherentBits rho / (1 - 2 * Real.sqrt delta) +
        4 * ((2 * Real.sqrt delta) * Real.logb 2
          ((Fintype.card A : ℝ) * Fintype.card B) + 1) / (1 - 2 * Real.sqrt delta) : ℝ) : EReal) ∧
    OperatorAttained rho delta := by sorry

end QAlgorithms.Papers.Independent.Advance50.P07

end
