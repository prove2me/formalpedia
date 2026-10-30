-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_lemma2
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.lemma2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:36:30.730195+00:00
-- url     : https://prove2.me/theorems/7380243f-289f-4225-a022-31107cef8860
-- title:
--   Lemma 2: character of the induced representation
-- statement:
--   For a Young diagram $\mu$, let $S^\mu$ be its complex Specht module, constructed as a Young left ideal, and $d_\mu=\dim S^\mu$. Restriction from $S_N$ to $S_{N-1}$ uses the subgroup fixing the last letter; induction uses this subgroup. Occurrence and multiplicity refer to actual modules, equivalently to dimensions of their intertwiner spaces.
--
--   Let $N\ge1$, $\alpha\vdash N-1$, and $\sigma\in S_N$ have $k$ fixed points. If $k=0$, the induced character is zero. If $k>0$, let $\bar\sigma\in S_{N-1}$ be obtained by conjugating any fixed letter to the last position and deleting that letter. All nontrivial cycles are unchanged. Then
--
--   $$
--   \chi_{\operatorname{Ind}S^\alpha}(\sigma)=k\chi_\alpha(\bar\sigma),\qquad
--   \chi_{\operatorname{Ind}S^\alpha}(e)=N d_\alpha.
--   $$
--
--   This includes the derangement case without subtracting one from zero.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 6, Lemma 2: character of the induced representation

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Lemma 2, Eqs.(18)–(19), with the proof's explicit zero-fixed-point case
(PDF pp.6–7). Conjugating a fixed letter to the last position and deleting it
preserves all nontrivial cycles and deletes exactly one 1-cycle. -/
theorem lemma2 {K : ℕ} (alpha : Partition (K+1) K) :
    (∀ pi : Equiv.Perm (Fin (K+1)),
      (fixedCount pi = 0 → (inducedAction alpha pi).trace = 0) ∧
      (∀ a : Fin (K+1), pi a = a →
        (inducedAction alpha pi).trace = (fixedCount pi : ℂ) *
          spechtCharacter alpha (deleteLast K (Equiv.swap a (Fin.last K) * pi * Equiv.swap a (Fin.last K))))) ∧
    (inducedAction alpha 1).trace = ((K+1) * irrepDim alpha : ℕ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
