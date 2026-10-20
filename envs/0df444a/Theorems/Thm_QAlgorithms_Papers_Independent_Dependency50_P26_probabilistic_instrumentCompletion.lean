-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_probabilistic_instrumentCompletion
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.probabilistic_instrumentCompletion
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:38:33.304992+00:00
-- url     : https://prove2.me/theorems/29fc3c2f-341a-40be-a32a-f1e1b90a89bb
-- title:
--   Theorem 9: completing a probabilistic comb to an instrument
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $R$ be a probabilistic $N$-comb, $N\ge1$: it is positive and dominated by a deterministic comb on the same signature. There exists a finite nonempty generalized instrument containing $R$ as a branch:
--
--   $$
--   \exists\{P_i\}_{i=1}^k,\qquad\sum_iP_i\text{ is deterministic},\quad P_i\succeq0,\quad R=P_{i_0}\text{ for some }i_0.
--   $$
--
--   Branch membership is witnessed explicitly; the claim is not just existence of an unrelated instrument.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 16, Theorem 9: completing a probabilistic comb to an instrument

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.16, Theorem 9: include the given probabilistic comb as an actual branch. -/
theorem probabilistic_instrumentCompletion (s : Signature) (n : ℕ)
    (R : Matrix (Basis s n) (Basis s n) ℂ) (hR : Probabilistic s n R) :
    ∃ k, ∃ P : Fin k → Matrix (Basis s n) (Basis s n) ℂ,
      CombInstrument s n k P ∧ ∃ i, P i = R := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
