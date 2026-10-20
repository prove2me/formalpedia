-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_partialSwap_capacity_endpoints
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.partialSwap_capacity_endpoints
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:17:47.526233+00:00
-- url     : https://prove2.me/theorems/8b690079-5798-4831-b841-6f2c20a43fdf
-- title:
--   Unnumbered partial-swap capacity endpoints
-- statement:
--   For $d\ge1$, let $S_p=\sqrt{1-p}I+i\sqrt p\,\mathrm{Swap}$ and $\mathcal S_p(X)=S_pXS_p^\dagger$. Let $C$ be the forward classical capacity with local CPTP interleavings and independent initial local states. No initial shared entanglement is supplied.
--
--   $$
--   C(\mathcal S_1)=2\log_2d,\qquad C(\mathcal S_0)=0.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** The p=1 result is credited to [30], but this paper gives its own achievable strategy and beta upper bound. Entanglement is first created and then renewed by subsequent uses.
--
--   **Round 1 domain audit** Round 1 restores d>=1: the source pp.19-20 assumes positive dimension and does not exclude the trivial system. At d=1 both endpoint channels are scalar identity channels, no message reaches Bob, and 2 log2 1=0. The d>=2 condition belongs to the separately displayed two-block Werner parametrization.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 19, Unnumbered partial-swap capacity endpoints

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.Elementwise

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P09

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Information100.P06 (traceOutput)

open QAlgorithms.Papers.Independent.Information100.P58 (testingD singleErasure)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P04 (werner)

/-- Unnumbered partial-swap capacity endpoints, arXiv:2010.01058v3, PDF pp.19,20.
The p=1 result is credited to [30], but this paper gives its own achievable strategy and beta upper bound. Entanglement is first created and then renewed by subsequent uses. The source imposes
only positive dimension here; d=1 has zero capacity at both endpoints. -/
theorem partialSwap_capacity_endpoints {d : ℕ} (hd : 0 < d) :
    forwardCapacity (partialSwap d 1) = ((2*Real.logb 2 d : ℝ) : EReal) ∧
      forwardCapacity (partialSwap d 0) = 0 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
