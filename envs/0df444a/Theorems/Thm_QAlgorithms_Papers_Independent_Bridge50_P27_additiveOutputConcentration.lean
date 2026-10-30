-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P27_additiveOutputConcentration
-- name    : QAlgorithms.Papers.Independent.Bridge50.P27.additiveOutputConcentration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:21:54.454095+00:00
-- url     : https://prove2.me/theorems/909686fa-3c0f-4bc2-8475-df0306a7ad9f
-- title:
--   Additive output total-photon concentration
-- statement:
--   Fix $N_S\ge0$ and a positive per-mode slack $d_5$. Let $\rho$ be an arbitrary normalized positive trace-class state on the complete $n$-mode Fock space, with no Gaussian, product, finite-rank or finite-energy restriction. Let $0\le e\le1$ and suppose $\operatorname{Tr}(\Pi_{\lceil nN_S\rceil}\rho)\ge1-e$. For fixed additive variance $v\ge0$, there exist a nonnegative tail $d_6(n)\to0$ and a positive threshold $n_0$, uniform over all such states and deficits, such that
--
--   $$\operatorname{Tr}\!\left[\Pi_{\lceil n(N_S+v+d_5)\rceil}\,\mathcal N_v^{\otimes n}(\rho)\right]\ge1-e-2\sqrt e-d_6(n)\qquad(n\ge n_0).$$
--
--   This is the stated additive extension in the form of the lemma it extends. The slack and error terms suppressed by the informal prose are retained; no exponential tail estimate is asserted.
-- source:
--   Strong converse rates for classical communication over thermal and additive noise bosonic channels, arXiv:1312.3287v2, PDF p. 15, §5.3, extension of Lemma 1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P27

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

-- Exact accepted definitions, checked against their complete source bodies.

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Dependency50.P24 (logBits)

open QAlgorithms.Papers.Independent.Renew46.P30 (photonTotal)

open QAlgorithms.Papers.Independent.Support50.P06 (totalEnergy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Section 5.3, PDF p.15: additive extension of Lemma 1, with its positive
per-use slack and errors retained. No exact-mean cutoff or uniform channel-limit
claim is introduced. v=0 remains included. -/
theorem additiveOutputConcentration (v NS d5 : ℝ)
    (hv : 0 ≤ v) (hNS : 0 ≤ NS) (hd5 : 0 < d5) :
    ∃ d6 : ℕ → ℝ, (∀ n, 0 ≤ d6 n) ∧ Tendsto d6 atTop (𝓝 0) ∧
      ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
        ∀ rho : S.State (B.NumberString n), ∀ deficit : ℝ,
        0 ≤ deficit → deficit ≤ 1 →
        1 - deficit ≤ totalPhotonCutoffMass (Nat.ceil ((n : ℝ) * NS)) rho.coefficients →
        1 - deficit - 2 * Real.sqrt deficit - d6 n ≤
          totalPhotonCutoffMass (Nat.ceil ((n : ℝ) * (NS + v + d5)))
            (additiveBlock v n rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P27

end
