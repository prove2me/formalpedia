-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_erasure_feedback_strongConverse
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.erasure_feedback_strongConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:19:52.131637+00:00
-- url     : https://prove2.me/theorems/ff760510-4563-4c07-ac1f-cee661dfa073
-- title:
--   Unnumbered erasure feedback strong converse (351)
-- statement:
--   For $d\ge2$ and $p\in[0,1]$, the erasure channel has input dimension $d$ and output dimension $d+1$: $E_{p,d}(X)=(1-p)X\oplus p\operatorname{Tr}(X)|e\rangle\langle e|$, with the erasure flag orthogonal to the transmitted space. Capacities allow arbitrary finite classical feedback, independent initial local states and local CPTP memories, with the inf-error liminf and sup-error limsup definitions.
--
--   $$
--   C_\leftarrow(E_{p,d})=\widetilde C_\leftarrow(E_{p,d})=(1-p)\log_2d.
--   $$
--
--   This is a structural property of the paper's forward communication measures.
--
--   **Formalization Note** The spurious rho argument in (351) is removed: capacity is a function of the channel. Both p=0 and p=1 are retained. The paper combines [21, Lemma 12] with its Corollary 31.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 21, Unnumbered erasure feedback strong converse (351)

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

/-- Unnumbered erasure feedback strong converse (351), arXiv:2010.01058v3, PDF pp.21.
The spurious rho argument in (351) is removed: capacity is a function of the channel. Both p=0 and p=1 are retained. The paper combines [21, Lemma 12] with its Corollary 31.
Source correction: Printed: (351) applies channel capacities to E_p,d(rho). Changed: Use the channel E_p,d as the capacity argument. Why: The preceding sentence and both operational definitions take a channel, not an output state. -/
theorem erasure_feedback_strongConverse {d : ℕ} (hd : 2 ≤ d) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    feedbackCapacity (erasureFin d p) = (((1-p)*Real.logb 2 d : ℝ) : EReal) ∧
      feedbackStrong (erasureFin d p) = (((1-p)*Real.logb 2 d : ℝ) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
