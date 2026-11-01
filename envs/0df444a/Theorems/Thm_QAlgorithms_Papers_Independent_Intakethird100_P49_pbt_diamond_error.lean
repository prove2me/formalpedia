-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_pbt_diamond_error
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.pbt_diamond_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:36:25.793215+00:00
-- url     : https://prove2.me/theorems/4116c175-a3f3-4e32-850a-ac33b69d2a96
-- title:
--   Lemma 1, Eqs.(8)–(10): PBT diamond error
-- statement:
--   Let $d\ge2$ and let $\Gamma_{d,M}$ be the deterministic PBT channel using integer $M\ge2$, $M$ normalized Bell pairs, the standard square-root measurement, classical communication of its outcome, and port selection. Let $f_e=\langle\Phi_d|(\mathrm{id}\otimes\Gamma_{d,M})(\Phi_d)|\Phi_d\rangle$, with normalized $|\Phi_d\rangle=d^{-1/2}\sum_j|j,j\rangle$. The channel is CPTP and depolarizing: $\Gamma(X)=(1-\xi_{d,M})X+\xi_{d,M}\operatorname{tr}(X)I/d$. Its actual unhalved diamond error satisfies
--
--   $$\delta_{d,M}=2(1-f_e)=\frac{2(d^2-1)}{d^2}\xi_{d,M}\le\frac{2d(d-1)}M.$$
--
--   Moreover $\delta_{d,M}\to0$ as integer $M\to\infty$. These identities relate the operational PBT construction to its depolarizing probability and give uniform convergence, including reference-entangled inputs.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 3, Lemma 1, Eqs.(8)–(10): PBT diamond error

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P49

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P49

open QAlgorithms Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

open QAlgorithms.Papers.Independent.Information100.P71 (diamond AdaptiveTest adaptiveInput adaptiveAccept)

open QAlgorithms.Papers.Independent.Bridge50.P25
  (LOCCOn normalizedChannelChoi TwoWayGenerationCode TwoWayChannelProtocol
   generationCodeError twoWayGenerationCapacity sendChannelRegister StateFunctional
   IsDimensionChangingLOCCMonotone privateStateInPartyOrder)

open QAlgorithms.Papers.Independent.Support50.P07 (amplitudeDampingChannel)

/-- Lemma 1, PDF p.3, (8)--(10), Methods pp.7--8: actual SRM PBT is
CPTP and depolarizing; full diamond error equals twice Bell infidelity.
The error bound is uniform over all inputs, including entangled references. -/
theorem pbt_diamond_error (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    (∀ M : ℕ, 2 ≤ M →
      IsChannel (pbtChannel d M) ∧
      (∀ X, pbtChannel d M X = ((1-pbtNumber d M : ℝ) : ℂ) • X +
        ((pbtNumber d M / d : ℝ) : ℂ) • (X.trace • (1 : Mat (Fin d)))) ∧
      pbtError d M = 2 * (1-pbtEntanglementFidelity d M) ∧
      pbtError d M = 2 * ((d : ℝ)^2-1) / (d : ℝ)^2 * pbtNumber d M ∧
      pbtError d M ≤ 2 * (d : ℝ) * (d-1 : ℝ) / M) ∧
    Tendsto (pbtError d) atTop (nhds 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
