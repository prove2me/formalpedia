-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P09_depolarizing_feedback_upperBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P09.depolarizing_feedback_upperBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:19:15.813984+00:00
-- url     : https://prove2.me/theorems/2bb7d874-7608-495f-a403-82179579e637
-- title:
--   Unnumbered depolarizing feedback bound (VII-C)
-- statement:
--   For $d\ge1$ and $p\in[0,1]$, put $D_p(X)=(1-p)X+p\operatorname{Tr}(X)I/d$. Let $C_\leftarrow$ be the ordinary maximum-error feedback capacity, with arbitrary finite classical feedback and independent local initial states, defined by the inf-error liminf prescription. Upsilon uses Umegaki entropy and arbitrary CP comparisons with $\beta\le1$.
--
--   $$
--   C_\leftarrow(D_p)\le\Upsilon(D_p).
--   $$
--
--   This gives the source's operational capacity conclusion in the stated assistance model.
--
--   **Formalization Note** This is the paper's novel feedback application. The unassisted Holevo formula and EB-regime equality are background; the qubit-only 1-h2(p/2) formula is not generalized to d>2.
--
--   **Round 1 domain audit** Round 1 restores d>=1: (348)-(349) and the feedback-bound paragraph impose no d>=2 restriction. For d=1, D_p(X)=X for every p in [0,1], and both the feedback capacity and Upsilon are zero. The source explicitly imposes d>=2 on the following erasure example, not this one.
-- source:
--   Bounding the forward classical capacity of bipartite quantum channels, arXiv:2010.01058v3, PDF p. 21, Unnumbered depolarizing feedback bound (VII-C)

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

/-- Unnumbered depolarizing feedback bound (VII-C), arXiv:2010.01058v3, PDF pp.21.
This is the paper's novel feedback application. The unassisted Holevo formula and EB-regime equality are background; the qubit-only 1-h2(p/2) formula is not generalized to d>2. Positive dimension includes
the trivial d=1 channel; Section VII-C does not impose d>=2. -/
theorem depolarizing_feedback_upperBound {d : ℕ} (hd : 0 < d) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    feedbackCapacity (depolarizing d p) ≤ pointUpsilon relativeD (depolarizing d p) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P09

end
