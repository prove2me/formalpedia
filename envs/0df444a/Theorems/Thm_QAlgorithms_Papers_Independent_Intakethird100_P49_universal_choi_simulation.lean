-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_universal_choi_simulation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.universal_choi_simulation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:38:25.935318+00:00
-- url     : https://prove2.me/theorems/ffb13dca-fc6f-4edb-b463-32516b687c3e
-- title:
--   Eqs.(12)–(14): universal multi-copy Choi simulation
-- statement:
--   Fix an input dimension $d\ge2$, output dimension $e\ge1$, and integer $M\ge2$. Let $T_{d,e,M}$ be the map explicitly obtained by Alice's standard PBT measurement and Bob's selection of the indicated output port; Alice's residual output is trivial. This map is trace-preserving LOCC and CPTP, and is fixed before the channel. For every CPTP channel $\mathcal E:d\to e$, its normalized Choi state $\rho_{\mathcal E}$, and every input operator $X$,
--
--   $$\mathcal E^M(X):=\mathcal E(\Gamma_{d,M}(X))=T_{d,e,M}(X\otimes\rho_{\mathcal E}^{\otimes M}),\qquad\|\mathcal E-\mathcal E^M\|_\diamond\le\delta_{d,M}.$$
--
--   The identity holds on all operators and therefore preserves reference coherences. The source attributes the underlying PBT simulation idea to reference [21]; the present bound applies also to rectangular channels.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 4, Eqs.(12)–(14): universal multi-copy Choi simulation

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

/-- PDF pp.3--4, (12)--(14): the explicitly computed selection LOCC is
independent of E; equality holds on all operators and hence with references.
The underlying PBT channel-simulation idea is attributed by the source to [21]. -/
theorem universal_choi_simulation (d e M : ℕ) [NeZero d] [NeZero e]
    (hd : 2 ≤ d) (hM : 2 ≤ M) :
    LOCCOn (pbtSelection d e M) ∧ IsChannel (pbtSelection d e M) ∧
    ∀ E : Superop (Fin d) (Fin e), IsChannel E →
      (∀ X a b, simulated E M X a b =
        pbtSelection d e M (pbtSimulationInput E M X) ((),a) ((),b)) ∧
      diamond (fun X => E X - simulated E M X) ≤ pbtError d M := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
