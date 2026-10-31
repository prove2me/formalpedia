-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P07_product_finite_size_bound
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P07.product_finite_size_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T04:54:59.042973+00:00
-- url     : https://prove2.me/theorems/91d6e541-fc3a-47e9-9718-8b626774e581
-- title:
--   §6.4.2 (6.97)–(6.100): product-state finite-size bound
-- statement:
--   All quantum systems below are finite-dimensional complex Hilbert spaces of positive dimension, and logarithms are binary. A normalized state is positive semidefinite with trace one; a subnormalized state has trace at most one. Marginals are partial traces. Here $F$ is squared algebraic fidelity, $F_*$ is squared generalized fidelity, $P=\sqrt{1-F_*}$ is purified distance, and $\Delta(\rho,\tau)=\max_{0\le M\le I}|\operatorname{Tr}((\rho-\tau)M)|$. The symbols $H_{\min}$ and $H_{\max}$ denote conditional min- and max-entropy, with values $+\infty$ and $-\infty$ at zero. Smoothing optimizes over all subnormalized states in the purified-distance ball; every entropy radius satisfies $0\le\varepsilon<\sqrt{\operatorname{Tr}\rho}$. Write $g(t)=-\log_2(1-\sqrt{1-t^2})$ for $0<t<1$.
--
--   For a finite set of normalized supported pairs (ρ_i,σ_i), choose a common C≥0 before all n and all sequences of pairs. For n≥1, (1/n)Dmax^ε(⊗ρ_i||⊗σ_i)≤(1/n)ΣD_i + (g(ε)+(1/(2log(e)n))ΣV_i)/sqrt(n)+C/n.
--
--   $$
--   \frac1nD_{\max}^\varepsilon(\bigotimes_i\rho_i\|\bigotimes_i\sigma_i)\le\frac1n\sum_iD_i+\frac1{\sqrt n}\left(g(\varepsilon)+\frac{\sum_iV_i}{2n\log_2e}\right)+\frac Cn.
--   $$
--
--   This result records the source’s operational or structural relation, with the stated endpoint and attainment clauses retained.
-- source:
--   Quantum Information Processing with Finite Resources -- Mathematical Foundations, arXiv:1504.00233v5, PDF p. 109, §6.4.2 (6.97)–(6.100): product-state finite-size bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07

noncomputable section

open Filter

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Intakenext100.P07

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J A B C D X Y Z : Type*}

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

variable [Fintype Z] [DecidableEq Z]

/-- NODE paper:1504.00233#6.noniid
§6.4.2 (6.97)–(6.100): product-state finite-size bound, arXiv:1504.00233v5, PDF p.109. -/
theorem product_finite_size_bound [Nonempty I] (S : Finset (paperMat I × paperMat I))
    (hS : ∀ x ∈ S, IsDensityMatrix x.1 ∧ IsDensityMatrix x.2 ∧ paperSupported x.1 x.2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ r s : Fin n → paperMat I, (∀ i, (r i,s i) ∈ S) →
      ∀ e : ℝ, 0 < e → e < 1 →
      ((1/(n:ℝ):ℝ):EReal)*smoothMaxD (productState r) (productState s) e ≤ (((∑ i, (paperRelativeD (r i) (s i)).toReal)/(n:ℝ)+
          (paperPenalty e+(∑ i, paperVariance (r i) (s i))/(2*Real.logb 2 (Real.exp 1)*(n:ℝ)))/Real.sqrt n+C/(n:ℝ):ℝ):EReal) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P07

end
