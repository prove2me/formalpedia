-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P44_multiparty_inner
-- name    : QAlgorithms.Papers.Independent.Dependency50.P44.multiparty_inner
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:31:30.090412+00:00
-- url     : https://prove2.me/theorems/2c9582f1-7937-41b3-9628-341cd4c89506
-- title:
--   Assisted inner region for m receivers
-- statement:
--   Let $m\ge1$ and let $\mathcal N:A'\to B_1\cdots B_m$ be a finite-dimensional memoryless quantum broadcast channel with a fixed Stinespring isometry. For any normalized pure input $\phi^{A_1\cdots A_mA'D}$ with unrestricted auxiliary dimensions and purifier $D$, form $\psi$ by applying that isometry to $A'$. Use entropy in bits and set $J(A_K)=\sum_{j\in K}H(A_j)-H(A_K)$, including $J(A_\varnothing)=0$.
--
--   With free independent pairwise entanglement between Alice and each receiver, every vector of nonnegative quantum rates satisfying
--
--   $$\sum_{j\in K}Q_j\le\tfrac12\left[\sum_{j\in K}I(A_j;B_j)_\psi-J(A_K)_\psi\right]
--   \qquad\text{for every }K\subseteq\{1,\ldots,m\}$$
--
--   is operationally achievable. A joint encoder sends independent EPR-entangled inputs, the receivers decode locally, and the entire product EPR target has vanishing unhalved trace-norm error, with liminf log-dimension rates per use. This is an inner region; it does not assert a multiparty converse.
-- source:
--   A father protocol for quantum broadcast channels, arXiv:quant-ph/0612155v4, PDF p. 7, VI.C / Eq. (21)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P44

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

open Filter Topology

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P44

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst)

/-- PDF p.7, VI.C, (21): all subset constraints give an assisted inner region for m receivers.
The printed n in the register labels is corrected to m; n does not denote block length here. -/
theorem multiparty_inner {m a : ℕ} (hm : 0 < m) {b : Fin m → ℕ} (N : Broadcast m a b)
    (S : InputState m (BroadcastBasis a)) :
    fatherRegion (broadcastOutputDensity N.channel S) ⊆ sourceQuantumAchievable N true := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P44

end
