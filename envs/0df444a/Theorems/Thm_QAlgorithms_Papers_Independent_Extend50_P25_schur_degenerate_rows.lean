-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P25_schur_degenerate_rows
-- name    : QAlgorithms.Papers.Independent.Extend50.P25.schur_degenerate_rows
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:25:33.547308+00:00
-- url     : https://prove2.me/theorems/c4762ffd-3e78-45a2-a9af-cadd32fc000a
-- title:
--   Lemma 4.2: probability estimate near degenerate rows
-- statement:
--   Fix $d\ge1$ and $c_1,\ldots,c_{d-1}\ge0$. There is $C>0$, depending only on these constants and $d$, such that for every $\gamma_1,\ldots,\gamma_{d-1}\ge0$, every integer $n\ge1$ and every partition $\alpha_1\ge\cdots\ge\alpha_d\ge0$ of $n$ satisfying $\alpha_i-\alpha_{i+1}\le c_i n^{\gamma_i}$, the following holds. Write $A_i=(\alpha_i-n/d)/\sqrt{n/d}$ and $\gamma_{ij}=\max_{i\le k<j}\gamma_k$. With $p_{d,n}(\alpha)=d_\alpha m_{d,\alpha}/d^n$ using the actual Specht and Weyl dimensions,
--   $$p_{d,n}(\alpha)\le C n^{-(d^2-1)/2+2\sum_{i<j}\gamma_{ij}}\prod_{i=1}^d\left(\frac{d(\alpha_i+1)}n\right)^{i-d-1/2}\exp\left(-\frac{\|A\|_1^2}{2d}\right).$$
--   The displayed bases are strictly positive. This controls the probability near adjacent-row degeneracies, uniformly over the exponents.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, PDF p. 20, Lemma 4.2: probability estimate near degenerate rows

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Lemma 4.2, PDF p.20: the constant depends only on c,d and is uniform in gamma,n,alpha.
The positive product bases d*(alpha_i+1)/n are algebraically the printed bases.
The one-based exponent i-d-1/2 is retained. -/
theorem schur_degenerate_rows (d : ℕ) (hd : 1 ≤ d) (c : Fin (d-1) → NNReal) :
    ∃ C : ℝ, 0 < C ∧ ∀ gamma : Fin (d-1) → NNReal,
      ∀ n : ℕ, 1 ≤ n → ∀ a : SchurDiagram d n,
      (∀ i : Fin (d-1),
        (((a.val ⟨i.val, by omega⟩).val : ℝ) - (a.val ⟨i.val+1, by omega⟩).val) ≤
          (c i : ℝ) * Real.rpow (n : ℝ) (gamma i : ℝ)) →
      schurMass a ≤ C * Real.rpow (n : ℝ)
        (-((d : ℝ)^2-1)/2 + 2 * ∑ i : Fin d, ∑ j : Fin d,
          if i < j then gammaInterval d gamma i j else 0) *
        (∏ i : Fin d, Real.rpow ((d : ℝ)*(((a.val i).val : ℝ)+1)/(n : ℝ))
          (((i.val : ℝ)+1) - (d : ℝ) - 1/2)) *
        Real.exp (-(∑ i : Fin d, |fluctuation a i|)^2/(2*(d : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P25

end
