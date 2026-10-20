-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_coherentLift
-- name    : QAlgorithms.Papers.Independent.Information100.P67.coherentLift
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:50:46.943971+00:00
-- url     : https://prove2.me/theorems/b00b52a1-daf7-4c55-946b-0f56bc429498
-- title:
--   Lemma 3.1 (Coherent lift of the joint criterion)
-- statement:
--   Let $U:A\to BE$ be a fixed finite-dimensional channel dilation and let $\mathcal C_n$ be any valid unassisted $(n,M)$ code. There are normalized purifications $|\phi_m\rangle_{S_1A^n}$ of its actual message states and local pure auxiliary systems such that the coherent encoder and decoder of (3.5)–(3.7) produce a normalized ket $|\omega\rangle_{KS\widehat KTE^n}$. Tracing out $S,T$ gives exactly the original code output. For some size-$M$ privacy test $\Pi$ constructed from unitary twisting blocks on $ST$,
--
--   $$\operatorname{Tr}[\Pi\,\omega_{KS\widehat KT}]\ge f(\mathcal C_n).$$
--
--   The sender prepares the uniform superposition with its retained message copy; the receiver uses the actual POVM square roots and retains its outcome copy. Thus the implementation uses no initial shared resource. This is the standard coherent correspondence credited by the paper, in its precise joint-fidelity convention.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 10, Lemma 3.1 (Coherent lift of the joint criterion)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Lemma 3.1, PDF pp.10–11 (standard correspondence credited there).
The coherent state is computed from actual message purifications and the
POVM square roots. Only local pure auxiliaries are introduced by its formula. -/
theorem coherentLift [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : IsIsometry U) {n : ℕ}
    (code : PrivateCode A B n) (hc : code.Valid) :
    ∃ r : ℕ, 0 < r ∧ ∃ pur : Fin code.M → EuclideanSpace ℂ (Fin r × (Fin n → A)),
      (∀ m, IsState (pur m) ∧ traceLeft (pureDensity (pur m)) = code.messages m) ∧
      ∃ t : ℕ, ∃ twist : Fin code.M →
        Matrix ((Fin code.M × Fin r) × ((Fin code.M × (Fin n → B)) × Option (Fin t)))
          ((Fin code.M × Fin r) × ((Fin code.M × (Fin n → B)) × Option (Fin t))) ℂ,
        (∀ m, twist m ∈ Matrix.unitaryGroup _ ℂ) ∧
        let psi := coherentCodeKet U code r t pur
        IsState psi ∧ coherentClassicalMarginal psi = jointOutput U code ∧
        optimizedFidelity U code ≤
          (privacyTest twist * traceRight (pureDensity psi)).trace.re := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
