-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P96_watrous_nonclosure
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P96.watrous_nonclosure
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T09:32:47.863235+00:00
-- url     : https://prove2.me/theorems/ee4a4af9-50be-4647-9fec-b099ce8434c9
-- title:
--   Watrous amplitude-product unitaries fail closure under composition and inverse
-- statement:
--   Fix a cyclic binary chain of length $L\ge5$ and its computational basis. A matrix is of Watrous form if a single translation-invariant local amplitude function $u$ satisfies $W(a\mid b)=\prod_x u(a_x\mid b_{x+N})$. Allow $N$ to be the whole ring, so this includes every smaller neighborhood. Let $H$ be the tensor product of single-qubit Hadamards, and let $P$ be the product of controlled-phase gates $\operatorname{diag}(1,1,1,-1)$ on all adjacent pairs. Then $H,P$ are unitary and
--
--   $$H,P\in\mathcal W_L,\qquad PH\notin\mathcal W_L,\qquad (PH)^*\in\mathcal W_L.$$
--
--   Here $\mathcal W_L$ denotes the matrices of Watrous form in this fixed basis. Thus composing two such unitaries can leave the class, and a member of the class can have its inverse outside it. The ring length is encoded as $L=5+e$ with $e\ge0$.
-- source:
--   Reversible quantum cellular automata, arXiv:quant-ph/0405174v1, PDF p. 14, §V.B: Watrous-form unitaries are not closed under composition or inverse

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96

noncomputable section

open scoped TensorProduct Kronecker BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P96

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

/-- §V.B, PDF pp.14--15: WQCA unitaries fail closure under product and inverse.
Phase pi and ring length at least five avoid the trivial short rings. -/
theorem watrous_nonclosure (extra : ℕ) :
    ringHadamard extra ∈ Matrix.unitaryGroup (RingConfiguration extra) ℂ ∧
    ringPhase extra ∈ Matrix.unitaryGroup (RingConfiguration extra) ℂ ∧
    IsWatrous extra (ringHadamard extra) ∧
    IsWatrous extra (ringPhase extra) ∧
    ¬ IsWatrous extra (ringPhase extra * ringHadamard extra) ∧
    IsWatrous extra (star (ringPhase extra * ringHadamard extra)) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P96

end
