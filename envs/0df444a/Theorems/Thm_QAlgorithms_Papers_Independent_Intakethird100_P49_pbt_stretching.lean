-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P49_pbt_stretching
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P49.pbt_stretching
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:39:47.684193+00:00
-- url     : https://prove2.me/theorems/283e5355-dd90-45b8-8db4-26870032b3cd
-- title:
--   Lemma 2 (PBT stretching), Eqs.(15)–(18)
-- statement:
--   Fix $d\ge2$, $e,o\ge1$, an integer $M\ge2$, and a fixed $n$-use adaptive protocol $P$ with arbitrary finite memory, normalized initialization, CPTP interleavings and an explicit CPTP terminal map to an $o$-dimensional output. Its operations are independent of the unknown channel. There is one CPTP map $\Lambda_{P,M}$, chosen before $\mathcal E$, such that for every CPTP $\mathcal E:d\to e$,
--
--   $$\rho_P(\mathcal E^M)=\Lambda_{P,M}(\rho_{\mathcal E}^{\otimes nM}),\qquad\|\rho_P(\mathcal E)-\rho_P(\mathcal E^M)\|_1\le n\|\mathcal E-\mathcal E^M\|_\diamond\le n\delta_{d,M}.$$
--
--   At $n=0$, the output is the channel-independent prepared and terminally processed state. For any actual two-party protocol initialized separably and consisting of dimension-changing trace-preserving LOCC interleaved with exactly $n$ channel transmissions, the approximate stretched output can be produced by a trace-preserving LOCC on the grouped $nM$ Choi resources, with full trace-norm error at most $n\delta_{d,M}$. This includes communication as well as general estimation and discrimination tasks.
-- source:
--   Fundamental limits to quantum channel discrimination, arXiv:1803.02834v4, PDF p. 4, Lemma 2 (PBT stretching), Eqs.(15)–(18)

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

/-- Lemma 2, PDF p.4, (15)--(18), Methods pp.8--9: common stretching map
for arbitrary tasks and every unknown channel. The additional two-party clause
uses separable preparation and actual finite dimension-changing LOCC execution. -/
theorem pbt_stretching (d e o n M : ℕ) [NeZero d] [NeZero e] [NeZero o]
    (hd : 2 ≤ d) (hM : 2 ≤ M) (P : AdaptiveProtocol d e o n) :
    (∃ L : Superop (Fin (n*M) → Fin d × Fin e) (Fin o), IsChannel L ∧
      ∀ E : Superop (Fin d) (Fin e), IsChannel E →
        adaptiveProtocolOutput P (simulated E M) = L (tensorPower (n*M) (normalizedChannelChoi E)) ∧
        traceNorm (adaptiveProtocolOutput P E - adaptiveProtocolOutput P (simulated E M)) ≤
          n * diamond (fun X => E X - simulated E M X) ∧
        n * diamond (fun X => E X - simulated E M X) ≤ n * pbtError d M) ∧
    (∀ (E : Superop (Fin d) (Fin e)), IsChannel E →
      ∀ (a b c f : ℕ), ∀ initial : Mat ((Fin (a+1) × Fin d) × Fin (b+1)),
        IsDensityMatrix initial → Entanglement.IsSeparableDensity initial →
        ∀ evolution : Superop ((Fin (a+1) × Fin d) × Fin (b+1))
          (Fin (c+1) × Fin (f+1)),
        TwoWayChannelProtocol E (Fin (c+1)) (Fin (f+1)) n a b evolution →
        ∃ L : Superop (Ports d (n*M) × Ports e (n*M)) (Fin (c+1) × Fin (f+1)),
          LOCCOn L ∧ IsChannel L ∧
          traceNorm (evolution initial - L (choiPorts E (n*M))) ≤ n * pbtError d M) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P49

end
