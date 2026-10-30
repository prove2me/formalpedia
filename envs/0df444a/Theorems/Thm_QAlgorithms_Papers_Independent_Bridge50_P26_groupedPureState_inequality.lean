-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P26_groupedPureState_inequality
-- name    : QAlgorithms.Papers.Independent.Bridge50.P26.groupedPureState_inequality
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:15:24.414416+00:00
-- url     : https://prove2.me/theorems/46e4fd1f-9577-49fc-82e9-a060cc560715
-- title:
--   Grouped pure-state inequality for unequal numbers of parties
-- statement:
--   Let $n,m$ be natural numbers with $n\le m$, and let $|\psi\rangle$ be one normalized pure state on positive finite-dimensional registers $S,P_1,\ldots,P_m,Q_1,\ldots,Q_n,E_1,E_2$. For any displayed grouping, evaluate $E_{\rm sq}$ on the marginal of $|\psi\rangle\langle\psi|$ on exactly the displayed registers. Here $E_{\rm sq}$ is the infimum of quantum conditional total correlation over every positive finite extension dimension and every normalized extension, in bits and without a factor $1/2$. Then
--
--   $$
--   \begin{aligned}
--   &E_{\rm sq}^{S:P_1Q_1:\cdots:P_nQ_n:P_{n+1}:\cdots:P_m}(\psi)\\
--   &\quad\le E_{\rm sq}^{SQ_1\cdots Q_nE_2:P_1:\cdots:P_m}(\psi)
--    +E_{\rm sq}^{SP_1\cdots P_mE_1:Q_1:\cdots:Q_n}(\psi).
--   \end{aligned}
--   $$
--
--   Thus the left side discards $E_1,E_2$, the first term on the right discards only $E_1$, and the second discards only $E_2$. Empty lists use unit tensor factors, and a single honest party has zero squashed entanglement. There is no independence assumption on any registers.
--
--   This inequality permits entanglement accounting when a broadcast channel distributes systems to different partition blocks. It is stated in the finite-dimensional source-proof interpretation; it does not supply an infinite-dimensional trace-class interface.
-- source:
--   Fundamental limitation on quantum broadcast networks, arXiv:1609.03994v3, PDF p. 12, Lemma 5, (A1)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P26

open QAlgorithms.Papers.Independent.Claimed50.P33 (multipartiteSquashed)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 5, PDF p.12, (A1): three honest reductions of ONE normalized pure
state, allowing n<=m and arbitrary positive finite local dimensions. No product
condition on the environments or auxiliary entropy equality is assumed. Empty
P/Q lists retain the unit empty tensor factor and the single-party zero convention. -/
theorem groupedPureState_inequality {m n : ℕ} (hnm : n ≤ m)
    {D : Fin (m + n + 3) → Type} [∀ i, Fintype (D i)]
    [∀ i, Nonempty (D i)]
    (psi : EuclideanSpace ℂ (PhysicalBasis D)) (hpsi : ‖psi‖ = 1) :
    groupedSquashed (pureDensity psi) (lemma5LeftGroups m n) ≤
      groupedSquashed (pureDensity psi) (lemma5FirstGroups m n) +
      groupedSquashed (pureDensity psi) (lemma5SecondGroups m n) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P26

end
