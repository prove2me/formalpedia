-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P57_reduced_state_transfer
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P57.reduced_state_transfer
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:11:40.321825+00:00
-- url     : https://prove2.me/theorems/d4bbca67-6f7a-4683-8d95-ebf7a379a34f
-- title:
--   Unnumbered transfer-operator formula for the reduced density matrix
-- statement:
--   Let $N,D\ge1$, let $A,\Phi,V$ be admissible RAGE data, and assume the raw MPS $M(A)$ is nonzero. Let $S$ be any subset of sites, including the empty or full set, and let $a,b$ be bit strings on $S$. Set $E_{k,u,v}=A_{k,u}\otimes\overline{A_{k,v}}$ and define
--
--   $$T_k(a,b)=\begin{cases}E_{k,a_k,b_k},&k\in S,\\ \sum_{t=0}^1 e^{it\sum_{j\in S}\Phi_{jk}(a_j-b_j)}E_{k,t,t},&k\notin S.\end{cases}$$
--
--   Let $\nu_{a,b}=\operatorname{tr}(T_1(a,b)\cdots T_N(a,b))$, let $G_S$ be the product of graph gates entirely within $S$, let $V_S=\bigotimes_{k\in S}V_k$, and let $Z=\|M(A)\|^2>0$. The reduced density matrix of the normalized RAGE vector is
--
--   $$\rho_S=\frac{V_S G_S\nu G_S^\dagger V_S^\dagger}{Z}.$$
--
--   This identity gives every marginal entry. The partial trace uses equal outside bra and ket bits. The summed physical bit in each outside transfer operator fixes the printed index omission; internal phases and rotations suppressed in the source are restored.
-- source:
--   Renormalization algorithm with graph enhancement, arXiv:0802.1211v1, PDF p. 2, Unnumbered transfer-operator formula for the reduced density matrix

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P57

noncomputable section

open scoped ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Intakethird100.P57

attribute [local instance] Classical.propDecidable

/-- PDF pp.2–3, reduced-state displays: full normalized identity with suppressed internal
phases and V restored. Printed/changed/why: the second double sum omits equality of traced
bra/ket bits; joinBits restores it as required by the preceding partial trace. The printed
B_l phase has an unbound outside label; transferT uses the summed t as required by gate action.
These are disclosed source corrections, requiring independent moderation. -/
theorem reduced_state_transfer {N D : ℕ} (hN : 1 ≤ N) (hD : 1 ≤ D)
    (A : Tensors N D) (G : PhaseGraph N) (V : Fin N → Matrix.unitaryGroup Bool ℂ)
    (hv : traceMPS A ≠ 0) (S : Finset (Fin N)) :
    0 < ‖traceMPS A‖ ^ 2 ∧ IsDensityMatrix (rageMarginal (rage A G V) S) ∧
    rageMarginal (rage A G V) S =
      (((‖traceMPS A‖ ^ 2 : ℝ) : ℂ)⁻¹) •
        (retainedOp G V S * crossMarginal A G S * (retainedOp G V S).conjTranspose) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P57

end
