-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_channel_specific_discrimination_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.channel_specific_discrimination_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:44:20.75022+00:00
-- url     : https://prove2.me/theorems/8e3d8155-46d3-4f1c-bf98-6bf85f102218
-- title:
--   §II.I, Eqs.(30)–(31): tightened channel-specific bound
-- statement:
--   Let $\mathcal E_0,\mathcal E_1:d\to e$ be CPTP, $d\ge2$, $e\ge1$, $n\ge1$, and integer $M\ge2$. Put $\mathcal E_u^M=\mathcal E_u\circ\Gamma_{d,M}$ and $\overline\Delta_M=(\|\mathcal E_0-\mathcal E_0^M\|_\diamond+\|\mathcal E_1-\mathcal E_1^M\|_\diamond)/2$, using unhalved diamond norms. Every common adaptive protocol has terminal states satisfying
--
--   $$\|\rho_n(0)-\rho_n(1)\|_1\le2n\overline\Delta_M+\|\rho_{\mathcal E_0}^{\otimes nM}-\rho_{\mathcal E_1}^{\otimes nM}\|_1.$$
--
--   Consequently
--
--   $$p_n\ge\frac{1-n\overline\Delta_M-D(\rho_{\mathcal E_0}^{\otimes nM},\rho_{\mathcal E_1}^{\otimes nM})}{2}.$$
--
--   This improves the universal estimate when the actual channel-specific simulation errors can be computed.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 6, §II.I, Eqs.(30)–(31): tightened channel-specific bound

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

/-- PDF p.6, (30)--(31): channel-specific full diamond errors, with their
arithmetic mean. The same physical test is used under both hypotheses. -/
theorem channel_specific_discrimination_bound (d e n M : ℕ) [NeZero d] [NeZero e]
    (hd : 2 ≤ d) (hn : 1 ≤ n) (hM : 2 ≤ M)
    (E0 E1 : Superop (Fin d) (Fin e)) (h0 : IsChannel E0) (h1 : IsChannel E1) :
    (∀ P : AdaptiveTest (Fin d) (Fin e) n,
      traceNorm (testOutput P E0 - testOutput P E1) ≤
        2*n*meanSimulationError M E0 E1 +
        traceNorm (tensorPower (n*M) (normalizedChannelChoi E0) -
          tensorPower (n*M) (normalizedChannelChoi E1))) ∧
    (1-n*meanSimulationError M E0 E1 - traceDistance
      (tensorPower (n*M) (normalizedChannelChoi E0))
      (tensorPower (n*M) (normalizedChannelChoi E1)))/2 ≤ symmetricAdaptiveError n E0 E1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
