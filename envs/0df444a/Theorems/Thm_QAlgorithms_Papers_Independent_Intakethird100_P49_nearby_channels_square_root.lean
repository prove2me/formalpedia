-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_nearby_channels_square_root
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.nearby_channels_square_root
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:41:51.025242+00:00
-- url     : https://prove2.me/theorems/7b0983ac-622d-4fef-8117-fc905121de94
-- title:
--   Eq.(27): finite square-root bound
-- statement:
--   Let $\mathcal E_0,\mathcal E_1:d\to e$ be CPTP, with $d\ge2$, $e\ge1$, and $n\ge1$. Set $\epsilon=1-F(\rho_{\mathcal E_0},\rho_{\mathcal E_1})$, the exact normalized-Choi root infidelity, so $0\le\epsilon\le1$, and choose integer $M_*=4d(d-1)n$. Then
--
--   $$p_n\ge B_{M_*}\ge\frac14-n\sqrt{2d(d-1)\epsilon}.$$
--
--   Here $p_n$ is the equal-prior optimal adaptive discrimination error, and $B_M$ the unclipped PBT expression. This is the exact finite square-root inequality of Eq. (27), separated from the source's unquantified exponential approximation.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 5, Eq.(27): finite square-root bound

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

/-- PDF p.5, exact first inequality of (27): epsilon is the EXACT Choi
infidelity. The following approximate exponential is separately deferred. -/
theorem nearby_channels_square_root (d e n : ℕ) [NeZero d] [NeZero e]
    (hd : 2 ≤ d) (hn : 1 ≤ n) (E0 E1 : Superop (Fin d) (Fin e))
    (h0 : IsChannel E0) (h1 : IsChannel E1) :
    let epsilon := 1-rootFidelity (normalizedChannelChoi E0) (normalizedChannelChoi E1)
    epsilon ∈ Set.Icc 0 1 ∧
    1/4 - n * Real.sqrt (2*(d : ℝ)*(d-1 : ℝ)*epsilon) ≤
      universalBound n (4*d*(d-1)*n) E0 E1 ∧
    1/4 - n * Real.sqrt (2*(d : ℝ)*(d-1 : ℝ)*epsilon) ≤ symmetricAdaptiveError n E0 E1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
