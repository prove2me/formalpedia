-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P80_lemma1
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P80.lemma1
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:29:04.173212+00:00
-- url     : https://prove2.me/theorems/264930d7-cbb3-408a-8415-6ad2f17bbfbb
-- title:
--   One local law matches any three setting pairs
-- statement:
--   Fix a normalized quantum-generated no-signalling experiment with two parties, two settings per party, and arbitrary nonempty finite outcome alphabets. For any omitted joint setting $s_0$, there is one probability law $\pi$ on the full tuple of potential outcomes such that
--
--   $$P_{s;\pi}=Q_s\qquad\text{for every }s\ne s_0.$$
--
--   Thus all three remaining outcome laws are reproduced simultaneously by the same local theory. No-signalling consistency is retained, and no condition is imposed on the omitted marginal.
-- source:
--   The statistical strength of nonlocality proofs, arXiv:quant-ph/0307125v2, PDF p. 31, Lemma 1: local compatibility of any three setting pairs

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P80

open scoped BigOperators ENNReal Topology Classical

open MeasureTheory Filter

/-- PDF pp.31–32, Lemma 1, including its extension to more than two outcomes.
One common local law fits the three retained settings simultaneously. -/
theorem lemma1 {S : BellExperiment} (hS : TwoByTwo S) (Q : Table S)
    (hQ : NonlocalityProof Q) (omitted : Settings S) :
    ∃ p : PiLocal S, ∀ s : Settings S, s ≠ omitted → localTable p.1 s = Q s := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P80

end
