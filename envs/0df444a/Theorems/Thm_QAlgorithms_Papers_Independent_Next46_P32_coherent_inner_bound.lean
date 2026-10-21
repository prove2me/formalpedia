-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P32_coherent_inner_bound
-- name    : QAlgorithms.Papers.Independent.Next46.P32.coherent_inner_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:29:49.137623+00:00
-- url     : https://prove2.me/theorems/93d23bf4-235f-450e-b44c-50d13a8f9688
-- title:
--   Unconditional Gaussian coherent-state inner bound
-- statement:
--   The channel acts on the full countable Fock space with independent fixed vacuum environment modes. Messages are independent and uniform on finite nonempty sets, arbitrary block density operators are allowed, and the receivers use separate POVMs. Let $\mathcal C$ denote the convex hull of the closure of achievable nonnegative rate pairs, measured in nats per use, using vanishing maximal joint error: Bob decodes both messages and Charlie decodes his own. The energy constraint is unconditional, averaged over messages and uses, with total block expectation at most $n\bar N$. Write $g(x)=(x+1)\ln(x+1)-x\ln x$, with $g(0)=0$.
--
--   For $1/2<\eta\le1$ and $\bar N\ge0$, the region in (16)-(17) is contained in $\mathcal C_{\mathrm{coh}}$ without any entropy-conjecture hypothesis. For every $0\le\beta\le1$, use circular complex normal modulation
--
--   $$
--   T\sim\mathcal{CN}(0,\bar N),\qquad
--   A\mid T=t\sim\mathcal{CN}(\sqrt{1-\beta}\,t,\beta\bar N).
--   $$
--
--   The variance parameter is total complex variance. At zero variance these laws mean Dirac masses. If $\rho_{B|t}$ and $\rho_{C|t}$ are the coherent mixtures after attenuation to the respective receivers and $\bar\rho_C$ is the unconditional mixture, then
--
--   $$
--   S(\rho_{B|t})=g(\eta\beta\bar N),\qquad
--   S(\rho_{C|t})=g((1-\eta)\beta\bar N),\qquad
--   S(\bar\rho_C)=g((1-\eta)\bar N).
--   $$
--
--   The conditional entropies are finite and integrable under the law of $T$, giving exactly the two rates in (16)-(17). Single-use encoding specifies the product coherent alphabet; reliable communication uses long codes and receiver-local collective decoding. Closure retains boundary rates and the full-Fock coherent limit described in note [15].
-- source:
--   Classical capacity of bosonic broadcast communication and a new minimum output entropy conjecture, arXiv:0706.3416v1, PDF p. 4, Section IV, Eqs. (18)-(21); note [15], PDF pp.12-13

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P32

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity productCoeff)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section IV, PDF pp.4-5,12-13, (18)-(21): unconditional product-coherent
inner bound, with exact Gaussian single-letter ensembles and boundary Dirac
laws. The capacity inclusion uses genuine long block codes and arbitrary
receiver-local collective decoding; no one-use vanishing-error claim is made. -/
theorem coherent_inner_bound (eta Nbar : ℝ)
    (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar) :
    thermalRegion eta (1 - eta) Nbar ⊆
      sourceRegion (fun n => broadcast n eta) Nbar true ∧
    ∀ beta : ℝ, 0 ≤ beta → beta ≤ 1 →
      IsProbabilityMeasure (complexNormal Nbar 0) ∧
      (∀ t, IsProbabilityMeasure
        (complexNormal (Nbar * beta) ((Real.sqrt (1 - beta) : ℂ) * t))) ∧
      (∀ t, spectralEntropyNats (conditionalCoherentMixture eta beta Nbar t) =
        ENNReal.ofReal (g (eta * beta * Nbar))) ∧
      Integrable (fun t : ℂ => (spectralEntropyNats (conditionalCoherentMixture eta beta Nbar t)).toReal)
        (complexNormal Nbar 0) ∧
      conditionalEntropyAverage eta beta Nbar = g (eta * beta * Nbar) ∧
      (∀ t, spectralEntropyNats (conditionalCoherentMixture (1 - eta) beta Nbar t) =
        ENNReal.ofReal (g ((1 - eta) * beta * Nbar))) ∧
      Integrable (fun t : ℂ =>
        (spectralEntropyNats (conditionalCoherentMixture (1 - eta) beta Nbar t)).toReal)
        (complexNormal Nbar 0) ∧
      spectralEntropyNats (averageCoherent (1 - eta) beta Nbar) =
        ENNReal.ofReal (g ((1 - eta) * Nbar)) ∧
      g ((1 - eta) * Nbar) - conditionalEntropyAverage (1 - eta) beta Nbar =
        g ((1 - eta) * Nbar) - g ((1 - eta) * beta * Nbar) := by sorry

end QAlgorithms.Papers.Independent.Next46.P32

end
