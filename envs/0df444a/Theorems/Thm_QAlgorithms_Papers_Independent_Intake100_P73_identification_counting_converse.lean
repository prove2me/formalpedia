-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P73_identification_counting_converse
-- name    : QAlgorithms.Papers.Independent.Intake100.P73.identification_counting_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:58:17.975411+00:00
-- url     : https://prove2.me/theorems/69ac7c5c-bdca-4c48-aef7-99d24d3184aa
-- title:
--   Han–Verdú counting converse, (18)
-- statement:
--   For a normalized discrete channel with finite input alphabet X, a positive integer M, and an identification code Phi, if the worst-input best full-L1 M-type approximation error is strictly less than 1-mu(Phi)-lambda(Phi), then |Phi| <= |X|^M. The code uses maximal first and second identification errors, and tuple approximants may repeat entries.
-- source:
--   General non-asymptotic and asymptotic formulas in channel resolvability and identification capacity and their application to wire-tap channel, arXiv:cs/0503088v2, PDF p. 6, Lemma 3 (Han–Verdú [2]), (18): identification/resolvability counting converse

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P73

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P73

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

/-- Hayashi PDF p.6, Lemma 3 (18), attributed to Han and Verdu [2].
Printed: an integer M. Changed: M>0, as required by the M-type code model;
at M=0 there is no nonempty approximating code. Strict separation is retained. -/
theorem identification_counting_converse {X Y : Type*} [Fintype X]
    (W : X → Y → ℝ≥0∞) (hW : IsDiscreteStochastic W)
    (c : IdentificationCode X Y) (M : ℕ) (hM : 0 < M)
    (hsep : (worstApproximation false M W).toReal <
      1 - firstError W c - secondError W c) :
    c.messages ≤ Fintype.card X ^ M := by sorry

end QAlgorithms.Papers.Independent.Intake100.P73

end
