-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P09_worstInput_symmetry_expansion
-- name    : QAlgorithms.Papers.Independent.Extend50.P09.worstInput_symmetry_expansion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T23:46:59.70874+00:00
-- url     : https://prove2.me/theorems/a100f3b9-8e0b-4b2b-abb5-3f1d8ef9563c
-- title:
--   Appendix D1: worst input and leading symmetry distance
-- statement:
--   Fix $d\ge2$ and Schmidt probabilities $p_i\ge0$ with $\sum_{i=1}^d p_i=1$. Let $|\psi_p\rangle=\sum_i\sqrt{p_i}|i\rangle_R|i\rangle_L$, $\psi_p^R=\operatorname{Tr}_L|\psi_p\rangle\langle\psi_p|$, and $\mathcal C_n(X)=X/n+(n-1)\operatorname{Tr}(X)I_d/(nd)$. Define
--   $$A(p)=\sqrt{\frac d2\sum_{i,j}\frac{p_ip_j}{p_i+p_j}-\frac14},$$
--   with each $0/0$ term equal to its continuous value zero. The purified-distance comparator error satisfies
--   $$P\!\left((\mathrm{id}\otimes\mathcal C_n)(\psi_p),\psi_p^R\otimes I_d/d\right)=\frac{A(p)}n+O(n^{-2}),\qquad A(p)\le\frac{\sqrt{d^2-1}}2.$$
--   Equality in the coefficient bound holds precisely when all $p_i=1/d$.
--
--   The expansion is for each fixed input, with constants allowed to depend on it; no full-rank Schmidt assumption is imposed. This identifies the maximal leading symmetry term rather than an individual random-code recovery error.
--
--   The fixed-comparator maximizer claim on p.12 is retained as well: for every $n\ge2$, the distance for $\psi_p$ is at most that for the normalized maximally entangled input $\Phi_d$, compared with $I_d/d\otimes I_d/d$ at that input. This concerns the averaged depolarizing channel and does not identify the worst input of each individual random encoder.
-- source:
--   Near-optimal covariant quantum error-correcting codes from random unitaries with symmetries, arXiv:2112.01498v2, PDF p. 22, Appendix D1: worst input and leading symmetry distance

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P09

noncomputable section

open scoped Matrix Matrix.Norms.Elementwise ComplexConjugate ENNReal ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Extend50.P09

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact generic definitions from the pinned accepted library.

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed bell)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalMinEntropy)

open QAlgorithms.Papers.Independent.Advance50.P02 (negLog)

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P09.covariantMatrixBorel

/-- Appendix D1, PDF p.22, (D14)–(D23), and the worst-input assertion
on p.12: fixed normalized Schmidt input, including zeros. The maximally
entangled input maximizes the fixed-comparator distance; the leading
coefficient is maximal precisely at uniform p. -/
theorem worstInput_symmetry_expansion (d : ℕ) (hd : 2 ≤ d)
    (p : Fin d → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (∀ n : ℕ, 2 ≤ n →
      pdist (idTensorSuperop (R := Fin d) (oneErasureMeanChannel d n) (pureDensity (schmidtKet p)))
        (Matrix.kronecker (traceRight (pureDensity (schmidtKet p))) (mixed (Fin d))) ≤
      pdist (idTensorSuperop (R := Fin d) (oneErasureMeanChannel d n) (pureDensity (bell (Fin d))))
        (Matrix.kronecker (mixed (Fin d)) (mixed (Fin d)))) ∧
    schmidtLeading p ≤ Real.sqrt ((d : ℝ)^2-1)/2 ∧
    (schmidtLeading p = Real.sqrt ((d : ℝ)^2-1)/2 ↔ ∀ i, p i = 1/(d : ℝ)) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n ≥ n0, 2 ≤ n →
      |pdist (idTensorSuperop (R := Fin d) (oneErasureMeanChannel d n) (pureDensity (schmidtKet p)))
        (Matrix.kronecker (traceRight (pureDensity (schmidtKet p))) (mixed (Fin d))) -
          schmidtLeading p/n| ≤ C/(n : ℝ)^2 := by sorry

end QAlgorithms.Papers.Independent.Extend50.P09

end
