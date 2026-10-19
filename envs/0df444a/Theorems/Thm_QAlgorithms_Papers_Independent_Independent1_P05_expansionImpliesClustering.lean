-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P05_expansionImpliesClustering
-- name    : QAlgorithms.Papers.Independent.Independent1.P05.expansionImpliesClustering
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:35:50.162061+00:00
-- url     : https://prove2.me/theorems/9492cd40-07db-477b-91d4-15fff942eee6
-- title:
--   Lemma 8: expansion implies clustering
-- statement:
--   Let $A\in\mathbb F_2^{m\times n}$ and $V\subseteq\mathbb F_2^n$. Let $\delta>0$ and $0<\mu<\nu$. Suppose every $x\in V$ with $|x|\le\nu n$ satisfies $|Ax|\ge(\delta/\mu)|x|$. Then
--   $$
--   x\in V,\quad |Ax|\le\delta n
--   \quad\Longrightarrow\quad
--   |x|\le\mu n\ \text{or}\ |x|\ge\nu n.
--   $$
--
--   This transfers small-set expansion to the clustering dichotomy. Both the size cutoff and syndrome cutoff use the number of columns $n$, even for rectangular matrices.
--
--   **Formalization Note** Positivity is taken from the proof and the paragraph immediately following Lemma 8; the unsupported zero-$\delta$ extension is excluded.
--
--   **Correction to the printed source.**
--
--   Printed: The displayed Lemma 8 omits its parameter domain; its proof uses delta>0 and mu>0 and the following paragraph takes mu<nu.
--
--   Corrected: State Lemma 8 on the meaningful positive regime delta>0 and 0<mu<nu, as pinned by the plan and proof.
--
--   Reason: For delta=0, an expansion hypothesis with beta=0 supplies no information and the claimed nontrivial dichotomy can fail. Independent moderation must confirm the intended domain.
-- source:
--   NLTS Hamiltonians from good quantum codes, arXiv:2206.13228v4, Lemma 8: expansion implies clustering, PDF p. 6. https://arxiv.org/abs/2206.13228v4 . PDF SHA-256: d7a1c5d8ee8ac147a6322005759342ac8154817d4e1534a9cc19b3da51b8875d.

import Definitions.Def_QAlgorithms_Defs_NLTSPreparationCircuits
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P05_Model
set_option autoImplicit false

/-! Statements from Anshu--Breuckmann--Nirkhe, arXiv:2206.13228v4.
Theorem 5 and three construction-specific expansion claims are deferred in HARD.md.
All new definitions are specific to this paper. -/

noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Independent1.P05

open PresentedCSS


































/-- Lemma 8, printed on PDF p.6 (Definitions 6--7 on p.5).
Positive parameters from its proof and following paragraph exclude delta=0. -/
theorem expansionImpliesClustering {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (V : Set (NLTSWord n)) (delta mu nu : ℝ) (hd : 0 < delta) (hm : 0 < mu)
    (hmn : mu < nu) (hexp : nltsExpanding A V nu (delta/mu)) :
    nltsClustering A V delta mu nu := by sorry


end QAlgorithms.Papers.Independent.Independent1.P05
