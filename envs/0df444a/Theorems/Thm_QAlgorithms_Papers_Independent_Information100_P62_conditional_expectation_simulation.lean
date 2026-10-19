-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_conditional_expectation_simulation
-- name    : QAlgorithms.Papers.Independent.Information100.P62.conditional_expectation_simulation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:34:49.07304+00:00
-- url     : https://prove2.me/theorems/36c841d6-26e2-43f2-80bb-e6cc08951483
-- title:
--   Lemma 3.3: exact conditional-expectation simulation
-- statement:
--   Represent $A=\bigoplus_k M_{d_k}(\mathbb C)$ on $L=\bigoplus_k\mathbb C^{d_k}$, and let $P_A(X)=\sum_kP_kXP_k$. For every channel $\Phi:L(H)\to L(K)$,
--   $$A\in\mathcal T(\Phi)\iff\exists\text{ channels }E:L(L)\to L(H),\ D:L(K)\to L(L),\quad D\Phi E=P_A.$$
--   The equality is on all matrices, including off-diagonal input blocks. This connects representation-based transmission to channel simulation.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 21, Lemma 3.3: exact conditional-expectation simulation

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.21, 22, 23, Lemma 3.3: exact conditional-expectation simulation. -/
theorem conditional_expectation_simulation [Nonempty I] [Nonempty O]
    (F : Superop I O) (hF : IsChannel F) (A : Shape) (hA : Valid A) :
    Transmits F A ↔ ∃ E : Superop (Logical A) I, ∃ D : Superop O (Logical A),
      IsChannel E ∧ IsChannel D ∧ D ∘ F ∘ E = pinching A := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
