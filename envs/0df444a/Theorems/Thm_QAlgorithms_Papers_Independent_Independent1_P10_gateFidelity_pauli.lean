-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Independent1_P10_gateFidelity_pauli
-- name    : QAlgorithms.Papers.Independent.Independent1.P10.gateFidelity_pauli
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T19:26:01.503956+00:00
-- url     : https://prove2.me/theorems/f88b99d2-557a-48bb-a474-d9b2229f7382
-- title:
--   Qubit Pauli formula for average gate fidelity
-- statement:
--   Let $\mathcal E$ be a completely positive trace-preserving map on a qubit, let $U$ be a unitary target, and let $\sigma_1=X$, $\sigma_2=Y$, $\sigma_3=Z$ be the Pauli matrices, with $Y=\begin{pmatrix}0&-i\\i&0\end{pmatrix}$. Then the normalized Haar gate overlap satisfies
--
--   $$\overline F(\mathcal E,U)=\frac12+\frac1{12}\sum_{j=1}^{3}\operatorname{Re}\operatorname{tr}(U\sigma_jU^\dagger\mathcal E(\sigma_j)).$$
--
--   This specializes the general operator-basis formula to three nonidentity Pauli operators; trace preservation suffices.
-- source:
--   A simple formula for the average gate fidelity of a quantum dynamical operation, arXiv:quant-ph/0205035v2, Eq. (18): qubit Pauli specialization, PDF p. 2. https://arxiv.org/abs/quant-ph/0205035v2 . PDF SHA-256: a59643207560eeaa2b638e69af6528c299e929c2eab2af32f0117a5d6a2f2f2a.

import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P10_Model
set_option autoImplicit false

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Independent1.P10
















/-- Nielsen, PDF p.2, Eq. (18): the X,Y,Z specialization for a qubit. Trace
preservation suffices; unitality is not a hypothesis. -/
theorem gateFidelity_pauli (E : Superop (Fin 2) (Fin 2)) (hE : IsChannel E)
    (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    gateFidelity 2 (by omega) E U = 1/2+(1/12 : ℝ)*
      ∑ j : Fin 3, ((U : Matrix (Fin 2) (Fin 2) ℂ)*pauliOperators j*
        star (U : Matrix (Fin 2) (Fin 2) ℂ)*E (pauliOperators j)).trace.re := by sorry


end QAlgorithms.Papers.Independent.Independent1.P10
