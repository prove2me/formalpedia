-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P96_diagonal_relative_unitaries
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P96.diagonal_relative_unitaries
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:32:03.20414+00:00
-- url     : https://prove2.me/theorems/b998a850-8f10-4c48-a806-1240e79c5dc8
-- title:
--   A summed commutator forces diagonal relative unitaries
-- statement:
--   Let $d\ge2$ and let $U_1,\ldots,U_d$ and $V_1,\ldots,V_d$ be unitary matrices on $\mathbb C^d$. In its fixed standard orthonormal basis write $P_\mu=|\mu\rangle\langle\mu|$. Suppose that for every pair $A,B\in M_d(\mathbb C)$,
--
--   $$\sum_{\mu,\nu}[U_\mu^*AU_\mu\otimes P_\mu,\;P_\nu\otimes V_\nu^*BV_\nu]=0.$$
--
--   There are unitary matrices $U,V$, chosen independently of the family index, such that
--
--   $$U^*U_\mu\text{ and }V^*V_\mu\text{ are diagonal for every }\mu.$$
--
--   The condition is on the entire sum of commutators. The conclusion provides a common reference unitary for each family.
-- source:
--   Reversible quantum cellular automata, arXiv:quant-ph/0405174v1, PDF p. 11, Lemma 9: diagonal relative unitaries

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

open scoped TensorProduct Kronecker BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P96

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

/-- Lemma 9, PDF p.11. The hypothesis is the sum of commutators in (30). -/
theorem diagonal_relative_unitaries (d : ℕ) (hd : 2 ≤ d)
    (U V : Fin d → Matrix.unitaryGroup (Fin d) ℂ)
    (hcomm : ∀ A B : Mat d,
      (∑ i : Fin d, ∑ j : Fin d,
        (((star (U i : Mat d) * A * (U i : Mat d)) ⊗ₖ coordinateProjection i) *
            (coordinateProjection j ⊗ₖ (star (V j : Mat d) * B * (V j : Mat d))) -
          (coordinateProjection j ⊗ₖ (star (V j : Mat d) * B * (V j : Mat d))) *
            ((star (U i : Mat d) * A * (U i : Mat d)) ⊗ₖ coordinateProjection i))) = 0) :
    ∃ Ubase Vbase : Matrix.unitaryGroup (Fin d) ℂ,
      ∀ k : Fin d, ∀ i j : Fin d, i ≠ j →
        (star (Ubase : Mat d) * (U k : Mat d)) i j = 0 ∧
        (star (Vbase : Mat d) * (V k : Mat d)) i j = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P96

end
