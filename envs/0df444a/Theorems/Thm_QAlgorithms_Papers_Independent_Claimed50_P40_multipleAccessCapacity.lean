-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P40_multipleAccessCapacity
-- name    : QAlgorithms.Papers.Independent.Claimed50.P40.multipleAccessCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:46:28.702439+00:00
-- url     : https://prove2.me/theorems/1f6f0e9b-9b23-4c03-9ea3-efa138e5e297
-- title:
--   Exact capacity region of a finite-dimensional quantum multiple-access channel
-- statement:
--   Let $s\ge1$ independent senders have finite nonempty alphabets $X_i$, and let $W:X_1\times\cdots\times X_s\to\mathcal S(\mathcal Y)$ be a channel into the normalized states of a finite-dimensional C*-algebra. There is one receiver with access to all of $\mathcal Y$. The channel is memoryless. A code uses separate deterministic sender encoders and an arbitrary output-block POVM; error is averaged over independent uniform messages.
--
--   Write $\mathcal C(W)$ for the nonnegative operational capacity region: for every error tolerance $\epsilon>0$ and rate slack $\delta>0$, codes with all rates at least $R_i-\delta$ and error at most $\epsilon$ exist at every sufficiently large positive block length. For a product input distribution $P=\bigotimes_i P_i$, let $\gamma_P$ be its channel state and define
--   $$
--   \mathcal P(P)=\left\{R\in\mathbb R_{\ge0}^s:\ \sum_{i\in J}R_i\le I_{\gamma_P}(X(J):Y\mid X(J^c))\ \text{for every }J\subseteq[s]\right\}.
--   $$
--   The exact capacity region is
--   $$
--   \mathcal C(W)=\overline{\operatorname{conv}\left(\bigcup_{P=\bigotimes_iP_i}\mathcal P(P)\right)}.
--   $$
--   Entropies and rates are in bits. The empty and full sender subsets are included; zero input probabilities are allowed. This identifies the operational region with a closed, convex, single-letter information region.
-- source:
--   The Capacity of the Quantum Multiple Access Channel, arXiv:quant-ph/9807019v3, PDF p. 6, Theorem 10

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 10, PDF p.6 (announced on p.1): exact classical-input multiple-access
capacity, retaining BOTH convexification and closure of the union over product input laws. -/
theorem multipleAccessCapacity {s : ℕ} (C : ClassicalChannel s) :
    capacityRegion (singleReceiver C) =
      closure (convexHull ℝ {R : Fin s → ℝ | ∃ P : InputLaw C.alphabet,
        R ∈ productLawRateRegion C P}) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P40

end
