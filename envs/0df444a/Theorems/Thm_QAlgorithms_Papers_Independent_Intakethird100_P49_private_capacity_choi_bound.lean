-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_private_capacity_choi_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.private_capacity_choi_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:48:25.039048+00:00
-- url     : https://prove2.me/theorems/211a56df-a9dc-4be4-8751-f09c6b458915
-- title:
--   Supplement V.B, Eqs.(187)–(190): operational key-capacity bound
-- statement:
--   Let $\mathcal E:d\to d$ be CPTP, $d\ge2$. Let $K(\mathcal E)$ be the operational supremum of two-way LOCC private-generation rates from separable initialization, arbitrary finite shields and vanishing full trace-norm error. Let $E_R$ denote finite state REE in bits. Define $\widetilde E_R(\mathcal E)$ as the supremum, over all positive finite memories and normalized $\rho_{a'ab'}$, of the finite real difference $E_R(a':bb')_{\mathcal E(\rho)}-E_R(a'a:b')_\rho$. Put $f(t)=(1+t)\log_2(1+t)-t\log_2t$, with $0\log0=0$. For every fixed integer $M\ge2$, PBT gives
--
--   $$\widetilde E_R(\mathcal E^M)\le E_R(\rho_{\mathcal E}^{\otimes M})\le M E_R(\rho_{\mathcal E}),$$
--
--   and both $\widetilde E_R(\mathcal E)$ and $K(\mathcal E)$ are at most $A_M=E_R(\rho_{\mathcal E}^{\otimes M})+\delta_{d,M}\log_2d+f(\delta_{d,M}/2)$. Furthermore
--
--   $$K(\mathcal E)\le A_M\le M E_R(\rho_{\mathcal E})+\frac{2d(d-1)}M\log_2d+f\!\left(\frac{d(d-1)}M\right)=K_M^{\rm UB}.$$
--
--   Consequently $K(\mathcal E)\le\inf_{M\in\mathbb N,\,M\ge2}K_M^{\rm UB}$. Integer $M$ is fixed before the coding limit. The accepted half-norm operational convention has the same vanishing-error capacity by tolerance rescaling. The initial cut in printed Eq. (184) is corrected from $b$ to $b'$, pending independent moderation.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 20, Supplement V.B, Eqs.(187)–(190): operational key-capacity bound

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

/-- Supplement V.B, PDF pp.19--20, (184),(187)--(190): integer-port
operational key-capacity bound and its amortized-REE ingredients. K is the
accepted actual two-way code-rate supremum; its half-norm error convention has
the same vanishing-error limit as the source's full-norm convention. The input
cut in (184) is corrected to (a',a):b'. Fixed M precedes all coding limits.
Independent moderation of the cut correction is required. -/
theorem private_capacity_choi_bound (d : ℕ) [NeZero d] (hd : 2 ≤ d)
    (E : Superop (Fin d) (Fin d)) (hE : IsChannel E) :
    (∀ M : ℕ, 2 ≤ M →
      amortizedREE (simulated E M) ≤ (realREE (choiPorts E M) : EReal) ∧
      realREE (choiPorts E M) ≤ M * realREE (normalizedChannelChoi E) ∧
      amortizedREE E ≤ ((realREE (choiPorts E M) + pbtError d M * Real.logb 2 d +
        capacityContinuity (pbtError d M/2) : ℝ) : EReal) ∧
      twoWayGenerationCapacity E true ≤ ((realREE (choiPorts E M) +
        pbtError d M * Real.logb 2 d + capacityContinuity (pbtError d M/2) : ℝ) : EReal) ∧
      ((realREE (choiPorts E M) + pbtError d M * Real.logb 2 d +
        capacityContinuity (pbtError d M/2) : ℝ) : EReal) ≤ (privateCapacityBound d M E : EReal)) ∧
    twoWayGenerationCapacity E true ≤
      ⨅ M : {m : ℕ // 2 ≤ m}, (privateCapacityBound d M.val E : EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
