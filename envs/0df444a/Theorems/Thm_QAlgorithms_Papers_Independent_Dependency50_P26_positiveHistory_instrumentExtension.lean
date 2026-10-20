-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_positiveHistory_instrumentExtension
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.positiveHistory_instrumentExtension
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:47:42.897961+00:00
-- url     : https://prove2.me/theorems/077329e5-61ee-4770-a8f5-dca9883dfc4b
-- title:
--   §VI question 1: any history can be an outcome after scaling
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $R\succeq0$ act on an ordered $N$-pair signature, $N\ge1$. Then some positive multiple of $R$ is a probabilistic comb and an actual branch of a finite generalized instrument:
--
--   $$
--   \exists a>0\ \exists\{P_i\},\qquad aR\text{ is probabilistic},\quad\{P_i\}\text{ is an instrument},\quad aR=P_{i_0}.
--   $$
--
--   This includes every rank-one history and the zero history. It imposes no positive probability requirement on the selected branch.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 20, §VI question 1: any history can be an outcome after scaling

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.21, question 1: every positive operator, including zero and rank-one histories,
can be positively scaled into a probabilistic comb and a branch of one instrument. -/
theorem positiveHistory_instrumentExtension (s : Signature) (n : ℕ) (hn : 0 < n)
    (R : Matrix (Basis s n) (Basis s n) ℂ) (hR : R.PosSemidef) :
    ∃ a : ℝ, 0 < a ∧ Probabilistic s n ((a : ℂ) • R) ∧
      ∃ k, ∃ P : Fin k → Matrix (Basis s n) (Basis s n) ℂ,
        CombInstrument s n k P ∧ ∃ i, P i = (a : ℂ) • R := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
