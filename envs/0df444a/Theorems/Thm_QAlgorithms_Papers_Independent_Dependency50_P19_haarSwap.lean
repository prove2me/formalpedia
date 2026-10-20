-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_haarSwap
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.haarSwap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:12:04.380361+00:00
-- url     : https://prove2.me/theorems/1c7d2bf1-0e6a-4b6b-b189-f92287bfc7a5
-- title:
--   Exact two-copy Haar swap average
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Let $A=A_1A_2$ and $R$ be finite nonempty registers. Write $F_A$ and $F_R$ for the swaps of the two corresponding copies and $\Pi_\pm=(I\pm F_A)/2$. Extend the swap $F_{A_2R}$ by identity on $A_1A_1'$. With normalized Haar measure,
--
--   $$
--   \int (U^\dagger\otimes U^\dagger\otimes I_{RR'})F_{A_2R}(U\otimes U\otimes I_{RR'})\,dU
--   =(p\Pi_++q\Pi_-)\otimes F_R,
--   \quad p=\frac{d_{A_1}+d_{A_2}}{d_A+1},\quad q=\frac{d_{A_1}-d_{A_2}}{d_A-1}.
--   $$
--
--   When $d_A=1$, both factors are singletons and $\Pi_-=0$; define its unused coefficient $q$ to be zero. No state hypothesis is needed.
--
--   This identity supplies the exact second moment used by the decoupling argument.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 7, Lemma IV.3, Eqs. (7)–(8)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma IV.3, PDF p.7, Eqs.(7)–(8). At a1=a2=1 the unused q coefficient
is assigned 0 by real total division; the antisymmetric projector is zero. -/
theorem haarSwap (a1 a2 r : ℕ) (ha1 : 0 < a1) (ha2 : 0 < a2) (hr : 0 < r) :
    (∫ U : Matrix.unitaryGroup (Fin (a1*a2)) ℂ,
      let T : Matrix ((Fin (a1*a2) × Fin (a1*a2)) × (Fin r × Fin r))
          ((Fin (a1*a2) × Fin (a1*a2)) × (Fin r × Fin r)) ℂ := Matrix.kronecker
        (Matrix.kronecker
          (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ)
          (U : Matrix (Fin (a1*a2)) (Fin (a1*a2)) ℂ))
        (1 : Matrix (Fin r × Fin r) (Fin r × Fin r) ℂ)
      Tᴴ * Matrix.kronecker (swapSecond a1 a2) (swap (Fin r)) * T
      ∂(Schur.unitaryHaar (a1*a2))) =
    Matrix.kronecker
      ((((a1 : ℝ)+(a2 : ℝ))/((a1*a2 : ℕ)+1) : ℝ) •
        ((1/2 : ℂ) • (1 + swap (Fin (a1*a2)))) +
       (((a1 : ℝ)-(a2 : ℝ))/(((a1*a2 : ℕ) : ℝ)-1) : ℝ) •
        ((1/2 : ℂ) • (1 - swap (Fin (a1*a2))))) (swap (Fin r)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
