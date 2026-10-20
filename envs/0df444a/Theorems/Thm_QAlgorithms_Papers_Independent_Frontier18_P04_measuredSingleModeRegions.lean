-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier18_P04_measuredSingleModeRegions
-- name    : QAlgorithms.Papers.Independent.Frontier18.P04.measuredSingleModeRegions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:50:43.046389+00:00
-- url     : https://prove2.me/theorems/9460b1e7-e7bf-4db5-8ca3-c22cf2fe07f4
-- title:
--   Operational homodyne and heterodyne coherent-state MAC regions
-- statement:
--   Let $m\ge1$ independent senders have transmissivities $\eta_i\ge0$ with $\sum_i\eta_i=1$, and mean photon budgets $\bar n_i\ge0$. Messages are independent and encoders use coherent states without entanglement between uses or senders. Let $\mathcal C_{\rm hom}$ and $\mathcal C_{\rm het}$ denote the closures of nonnegative rate vectors achievable with arbitrarily small average decoding error over long blocks, using respectively homodyne and heterodyne measurements followed by arbitrary classical block decoding. Rates are nats per channel use. Then
--
--   $$
--   \begin{aligned}
--   \mathcal C_{\rm hom}&=\left\{R\ge0:\ \sum_{i\in S}R_i\le\tfrac12\log\!\left(1+4\sum_{i\in S}\eta_i\bar n_i\right)\ \text{for every }S\subseteq\{1,\ldots,m\}\right\},\\
--   \mathcal C_{\rm het}&=\left\{R\ge0:\ \sum_{i\in S}R_i\le\log\!\left(1+\sum_{i\in S}\eta_i\bar n_i\right)\ \text{for every }S\subseteq\{1,\ldots,m\}\right\}.
--   \end{aligned}
--   $$
--
--   For two users, take $(\eta_1,\eta_2)=(\eta,1-\eta)$; the two singleton subsets and full subset give (5) and (6). The empty subset contributes $0\le0$. Zero budgets and zero transmissivities are included. These formulas quantify the rates of the specified optical measurements.
--
--   **Formalization Note** The source explicitly identifies these measured channels with scalar Gaussian noise of variance $1/4$ and two-dimensional Gaussian noise of variance $1/2$ in each coordinate. The capacity objects are constructed from those channel laws, separate finite-message encoders, measurable decoders, average energy, and average error.
-- source:
--   Multiple-Access Bosonic Communications, arXiv:quant-ph/0506171v2, PDF p. 2, §II.B, (5)–(8): single-mode homodyne/heterodyne capacity regions

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P04

noncomputable section

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology NNReal

namespace QAlgorithms.Papers.Independent.Frontier18.P04

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

/-- arXiv:quant-ph/0506171v2, PDF p.2,(5)–(8): exact operational coherent-state
regions for homodyne and heterodyne. The m=2 case with eta=(eta,1-eta)
is precisely (5),(6); all subsets give the individual and sum bounds.
Zero energies, disconnected users, and the empty subset are included. -/
theorem measuredSingleModeRegions (m : ℕ) (hm : 1 ≤ m)
    (eta nbar : Fin m → ℝ) (heta : ∀ i, 0 ≤ eta i)
    (hsum : ∑ i, eta i = 1) (hnbar : ∀ i, 0 ≤ nbar i) :
    homodyneCapacity eta nbar =
      {R | (∀ i, 0 ≤ R i) ∧ ∀ S : Finset (Fin m),
        (∑ i ∈ S, R i) ≤ (1 / 2) * Real.log (1 + 4 * ∑ i ∈ S, eta i * nbar i)} ∧
    heterodyneCapacity eta nbar =
      {R | (∀ i, 0 ≤ R i) ∧ ∀ S : Finset (Fin m),
        (∑ i ∈ S, R i) ≤ Real.log (1 + ∑ i ∈ S, eta i * nbar i)} := by sorry

end QAlgorithms.Papers.Independent.Frontier18.P04

end
