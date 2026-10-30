-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P36_quasiBellGram
-- name    : QAlgorithms.Papers.Independent.Advance50.P36.quasiBellGram
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T13:52:30.435169+00:00
-- url     : https://prove2.me/theorems/69543b10-1514-4885-b469-7a81305af18b
-- title:
--   Gram matrix of the four quasi-Bell coherent states
-- statement:
--   Let $\alpha\ne0$ be a finite complex amplitude and set $\kappa=e^{-2|\alpha|^2}$, $h_+=1/\sqrt{2(1+\kappa^2)}$, and $h_-=1/\sqrt{2(1-\kappa^2)}$. In the full two-mode Fock space define
--   $$
--   \begin{aligned}
--   \Psi_1&=h_+(|\alpha,\alpha\rangle+|-\alpha,-\alpha\rangle),&
--   \Psi_2&=h_-(|\alpha,\alpha\rangle-|-\alpha,-\alpha\rangle),\\
--   \Psi_3&=h_+(|\alpha,-\alpha\rangle+|-\alpha,\alpha\rangle),&
--   \Psi_4&=h_-(|\alpha,-\alpha\rangle-|-\alpha,\alpha\rangle).
--   \end{aligned}
--   $$
--   The coherent factors have their canonical coefficients and unit norms, and all four vectors are normalized. With $D=2\kappa/(1+\kappa^2)$, their Gram matrix in this order is
--   $$
--   (\langle\Psi_i|\Psi_j\rangle)_{i,j=1}^4=
--   \begin{pmatrix}1&0&D&0\\0&1&0&0\\D&0&1&0\\0&0&0&1\end{pmatrix}.
--   $$
--   This identifies the sole off-diagonal overlap and, in particular, the orthogonality of the odd pair. The overlap parameter is determined by the amplitude, rather than being an unrelated complex variable.
--
--   **Formalization Note** The finite labels $0,1,2,3$ follow the displayed order $\Psi_1,\ldots,\Psi_4$. Inner products are conjugate-linear in the first argument.
-- source:
--   Error free Quantum Reading by Quasi Bell State of Entangled Coherent States, arXiv:1108.4163v2, PDF p. 2, §II.B, Eqs.(5)-(6)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P36

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P36

open QAlgorithms.Papers.Independent.Frontier30.P21
  (WordFock coherentWord CoherentWordRealized binaryErrorValues)

open scoped Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.2, Eq.(6): the full Gram matrix in the printed Psi1,...,Psi4 order.
Actual canonical coherent factors and all four unit norms are conclusions;
kappa is the real antipodal overlap determined by alpha. -/
theorem quasiBellGram (alpha : ℂ) (halpha : alpha ≠ 0) :
    QuasiBellCoherentRealized alpha ∧
    (∀ i : Fin 4, ‖quasiBellState alpha i‖ = 1) ∧
    (let D : ℂ := (2 * antipodalOverlap alpha / (1 + antipodalOverlap alpha ^ 2) : ℝ)
     (fun i j : Fin 4 => inner (𝕜 := ℂ) (quasiBellState alpha i)
       (quasiBellState alpha j)) =
       !![1, 0, D, 0; 0, 1, 0, 0; D, 0, 1, 0; 0, 0, 0, 1]) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P36

end
