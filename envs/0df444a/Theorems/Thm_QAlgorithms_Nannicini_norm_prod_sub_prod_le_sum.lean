-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_norm_prod_sub_prod_le_sum
-- name    : QAlgorithms.Nannicini.norm_prod_sub_prod_le_sum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:51:34.872808+00:00
-- url     : https://prove2.me/theorems/27138c26-cc93-489d-8787-8da807ef63d0
-- title:
--   Errors of a product of unitaries add up
-- statement:
--   Let $q,T\ge 0$ and let $U_1,\dots,U_T$ and $U_1',\dots,U_T'$ be unitary $2^q\times 2^q$ matrices (gates on $q$ qubits). Write $\|A\|=\sup_{\|x\|=1}\|Ax\|$ for the operator norm induced by the Euclidean norm (Def. 1.35). Then
--
--   $$
--   \|U_1U_2\cdots U_T-U_1'U_2'\cdots U_T'\|\le\sum_{j=1}^{T}\|U_j-U_j'\| .
--   $$
--
--   The total error of a circuit is therefore at most the sum of the errors of its gates. To approximate a circuit with $m$ gates to precision $\epsilon$, it suffices to approximate each gate to precision $\epsilon/m$.
--
--   **Formalization Note** For $T=0$ both products are the identity and the statement reads $0\le0$.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 31, Proposition 1.46. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_Adiabatic
set_option autoImplicit false

namespace QAlgorithms.Nannicini

open QAlgorithms



/-- Nannicini, Proposition 1.46, PDF p. 31. Let `U_1 U_2 ⋯ U_T` and `U'_1 U'_2 ⋯ U'_T` be two
sequences of unitaries of the same length. Then
`‖U_1 U_2 ⋯ U_T − U'_1 U'_2 ⋯ U'_T‖ ≤ Σ_{j=1}^T ‖U_j − U'_j‖`, where `‖·‖` is the operator norm
induced by the Euclidean norm (Def. 1.35).

The unitaries act on `q` qubits (Postulate 2); the source's `U_j` is `U (j − 1)` and its
`U'_j` is `V (j − 1)`, and the products are taken in the source's left-to-right order,
`(List.ofFn U).prod = U 0 * ⋯ * U (T−1)`. At `T = 0` both products are `1` and the bound reads
`0 ≤ 0`. -/
theorem norm_prod_sub_prod_le_sum (q T : ℕ) (U V : Fin T → Matrix (Qubits q) (Qubits q) ℂ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Qubits q) ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup (Qubits q) ℂ) :
    specNorm ((List.ofFn U).prod - (List.ofFn V).prod) ≤ ∑ j, specNorm (U j - V j) := by
  sorry


end QAlgorithms.Nannicini
