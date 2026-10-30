-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P27_thermalOutputConcentration
-- name    : QAlgorithms.Papers.Independent.Bridge50.P27.thermalOutputConcentration
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:20:58.152754+00:00
-- url     : https://prove2.me/theorems/f9515718-10a6-4cf3-98f4-0e83f76813a3
-- title:
--   Thermal output total-photon concentration
-- statement:
--   Fix $N_S\ge0$ and a positive per-mode slack $d_5$. Let $\rho$ be an arbitrary normalized positive trace-class state on the complete $n$-mode Fock space, with no Gaussian, product, finite-rank or finite-energy restriction. Let $0\le e\le1$ and suppose $\operatorname{Tr}(\Pi_{\lceil nN_S\rceil}\rho)\ge1-e$. For fixed $0\le\eta\le1$ and $N_B\ge0$, there exist a nonnegative tail $d_6(n)\to0$ and a positive threshold $n_0$, uniform over $\rho$ and $e$, such that for every $n\ge n_0$,
--
--   $$\operatorname{Tr}\!\left[\Pi_{\lceil n(\eta N_S+(1-\eta)N_B+d_5)\rceil}\,\mathcal E_{\eta,N_B}^{\otimes n}(\rho)\right]\ge1-e-2\sqrt e-d_6(n).$$
--
--   Consequently the output remains concentrated when the input deficit vanishes. The per-mode slack is the reading used in the proof summations, correcting the constant total slack printed in the lemma display.
-- source:
--   Strong converse rates for classical communication over thermal and additive noise bosonic channels, arXiv:1312.3287v2, PDF p. 12, Lemma 1

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

/-- Lemma 1, PDF pp.12–15. CORRECTION: cutoff ceil(n*(eta*NS+(1-eta)*NB+d5))
is the one in (40)–(43) and the p.15 summation, rather than a constant total slack.
The uniform d6 and eventual n0 precede ALL density inputs, including states
with all permitted photons in one mode. No exponential tail rate is asserted. -/
theorem thermalOutputConcentration (eta NB NS d5 : ℝ)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (hNB : 0 ≤ NB)
    (hNS : 0 ≤ NS) (hd5 : 0 < d5) :
    ∃ d6 : ℕ → ℝ, (∀ n, 0 ≤ d6 n) ∧ Tendsto d6 atTop (𝓝 0) ∧
      ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
        ∀ rho : S.State (B.NumberString n), ∀ deficit : ℝ,
        0 ≤ deficit → deficit ≤ 1 →
        1 - deficit ≤ totalPhotonCutoffMass (Nat.ceil ((n : ℝ) * NS)) rho.coefficients →
        1 - deficit - 2 * Real.sqrt deficit - d6 n ≤
          totalPhotonCutoffMass (Nat.ceil ((n : ℝ) * (eta * NS + (1 - eta) * NB + d5)))
            (thermalBlock eta NB n rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P27

end
