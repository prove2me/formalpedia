-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_adaptive_discrimination_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.adaptive_discrimination_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:35:45.448948+00:00
-- url     : https://prove2.me/theorems/7b97f135-48a0-424c-a287-7f06dde06d19
-- title:
--   Theorem 3, Eq.(20): universal adaptive channel-discrimination lower bound
-- statement:
--   Let $\mathcal E_0,\mathcal E_1:\mathbb C^d\to\mathbb C^e$ be CPTP channels, with $d\ge2$ and $e\ge1$. Their equally likely labels are unknown to the adaptive protocol. Let $p_n$ be the infimum of the error over normalized preparations, arbitrary finite memories, label-independent CPTP interleavings, exactly $n$ channel calls, and final binary POVMs. Write $\rho_u$ for the normalized, reference-first Choi state and $D(\rho,\sigma)=\|\rho-\sigma\|_1/2$. For integer $M\ge2$, let $\delta_{d,M}$ be the unhalved diamond error of standard deterministic $M$-port PBT and define
--
--   $$B_M=\frac{1-n\delta_{d,M}-D(\rho_0^{\otimes nM},\rho_1^{\otimes nM})}{2}.$$
--
--   For every $n\ge1$, $p_n\ge B_M$ for every such $M$, and hence $p_n\ge\sup_{M\ge2}B_M$. Also $p_0=1/2$. No distinctness premise or finite optimizer is required. This is an operational bound uniform over all adaptive discrimination strategies.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 4, Theorem 3, Eq.(20): universal adaptive channel-discrimination lower bound

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

/-- Theorem 3, PDF p.4, (20): every integer M gives a universal lower bound;
no finite maximizer is asserted. The no-probing case has error exactly 1/2. -/
theorem adaptive_discrimination_lower_bound (d e : ℕ) [NeZero d] [NeZero e]
    (hd : 2 ≤ d) (E0 E1 : Superop (Fin d) (Fin e))
    (h0 : IsChannel E0) (h1 : IsChannel E1) :
    symmetricAdaptiveError 0 E0 E1 = 1/2 ∧
    (∀ n : ℕ, 1 ≤ n → ∀ M : ℕ, 2 ≤ M →
      universalBound n M E0 E1 ≤ symmetricAdaptiveError n E0 E1) ∧
    (∀ n : ℕ, 1 ≤ n →
      (⨆ M : {m : ℕ // 2 ≤ m}, universalBound n M.val E0 E1) ≤ symmetricAdaptiveError n E0 E1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
