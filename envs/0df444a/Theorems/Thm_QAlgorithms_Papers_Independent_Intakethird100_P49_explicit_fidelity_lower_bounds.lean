-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_explicit_fidelity_lower_bounds
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.explicit_fidelity_lower_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:40:50.864457+00:00
-- url     : https://prove2.me/theorems/da1fc666-e547-422c-96de-e51ac9594387
-- title:
--   Eqs.(24)–(26): explicit fidelity bounds
-- statement:
--   For CPTP channels $\mathcal E_0,\mathcal E_1:d\to e$, $d\ge2$, $e\ge1$, and $n\ge1$, let $F$ be the root fidelity of their normalized Choi states, and let $B_M$ be the universal PBT bound. For every integer $M\ge2$,
--
--   $$B_M\ge\frac12-\frac12\sqrt{1-F^{2nM}}-\frac{d(d-1)n}{M}.$$
--
--   If $x>2$ and $M=xd(d-1)n$ is an admissible integer, this reads $B_M\ge1/2-1/x-\sqrt{1-F^{2nM}}/2$, with $2nM=2xd(d-1)n^2$. At the integer choice $M_*=4d(d-1)n$,
--
--   $$p_n\ge B_{M_*}\ge\frac{1-2\sqrt{1-F^{8d(d-1)n^2}}}{4}.$$
--
--   These explicit finite-use bounds retain the port-integrality requirement and require no assertion that a best finite port count exists.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 5, Eqs.(24)–(26): explicit fidelity bounds

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

/-- PDF p.5, (24)--(26): fidelity lower bounds at admissible INTEGER port
counts. The x-parametrization is used only when x*d*(d-1)*n is such an integer. -/
theorem explicit_fidelity_lower_bounds (d e n : ℕ) [NeZero d] [NeZero e]
    (hd : 2 ≤ d) (hn : 1 ≤ n) (E0 E1 : Superop (Fin d) (Fin e))
    (h0 : IsChannel E0) (h1 : IsChannel E1) :
    let F := rootFidelity (normalizedChannelChoi E0) (normalizedChannelChoi E1)
    (∀ M : ℕ, 2 ≤ M →
      1/2 - Real.sqrt (1-F^(2*n*M))/2 - (d : ℝ)*(d-1 : ℝ)*n/M ≤
        universalBound n M E0 E1) ∧
    (∀ (x : ℝ), 2 < x → ∀ M : ℕ, 2 ≤ M →
      (M : ℝ) = x*d*(d-1 : ℝ)*n →
      1/2 - 1/x - Real.sqrt (1-F^(2*n*M))/2 ≤ universalBound n M E0 E1) ∧
    ((1-2*Real.sqrt (1-F^(8*d*(d-1)*n^2)))/4 ≤
      universalBound n (4*d*(d-1)*n) E0 E1 ∧
      universalBound n (4*d*(d-1)*n) E0 E1 ≤ symmetricAdaptiveError n E0 E1) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
