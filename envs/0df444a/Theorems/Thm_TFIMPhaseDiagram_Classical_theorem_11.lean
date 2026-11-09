-- Prove2me | Theorems.Thm_TFIMPhaseDiagram_Classical_theorem_11
-- name    : TFIMPhaseDiagram.Classical.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:02:45.656669+00:00
-- url     : https://prove2.me/theorems/bb0beb43-f792-4b9e-a60b-bc8909b940a5
-- title:
--   Theorem 11 — Classical approximation of the partition function and Pauli observables
-- statement:
--   Let $n\ge1$, let $J\in\mathbb R^{n\times n}$ be symmetric, and let $h,\eta\in\mathbb R^n$ be arbitrary signed site-dependent fields. Define $H=\frac12\sum_{i,j}J_{ij}Z_iZ_j+\sum_i h_iZ_i+\sum_i\eta_iX_i$, $Z=\operatorname{Tr}(e^H)$, $\rho=e^H/Z$, $\eta_{\min}=\min_i|\eta_i|$, and $\alpha(t)=\tanh(t)/t$ with $\alpha(0)=1$. Assume the non-strict threshold $\Delta(J)\alpha(\eta_{\min})\le1$.
--
--   One uniform randomized classical Real RAM program, with universal polynomial constants preceding every input, takes $\epsilon,\delta\in(0,1)$ and any of the following queries:
--
--   1. It estimates the partition function with $\Pr[\widehat Z=\exp(\pm\epsilon)Z]\ge1-\delta$.
--   2. For every $S\subseteq[n]$, including $S=\varnothing$, it estimates $\theta_S=\operatorname{Tr}(X_S\rho)$ with $\Pr[\widehat\theta_S=\exp(\pm\epsilon)\theta_S]\ge1-\delta$.
--   3. For every Pauli string $O\in\{I,X,Y,Z\}^{\otimes n}$, it estimates $\operatorname{Tr}(O\rho)$ with additive error at most $\epsilon$ and probability at least $1-\delta$.
--
--   The runtime is
--   $$\operatorname{poly}(n,\max_{i,j}|J_{ij}|,\max_i|h_i|,\max_i|\eta_i|,\epsilon^{-1})\log(\delta^{-1}).$$
--   Signed multiplicative accuracy means equality to a factor in $[e^{-\epsilon},e^\epsilon]$ times the true value; at zero the output must be exactly zero. All three guarantees belong to this single theorem. The diagonal of $J$ is allowed, and no degree, sparsity, field-sign, rationality, or strict-slack condition is imposed.
--
--   Differences from the source:
--   - encoding: poly(n,max|J|,max|h|,max|eta|,epsilon^-1) log(1/delta) time → one finite program and uniform natural C,d, charged goalBudget with 1+ceil(log(1/delta)); reason: The additive 1 gives a valid integer budget for every delta in (0,1) and has the source logarithmic asymptotic order. Query tags encode all three clauses without restricting fields or the equality threshold.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, printed p.7 = PDF p.7, Theorem 11

import Definitions.Def_TFIMPhaseDiagram_Classical_ram

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
/-- Theorem 11, pp.7-8, all three clauses in one uniform Real RAM program.
The query-dependent GoodOutput predicate gives the two signed multiplicative guarantees
and the arbitrary-Pauli additive guarantee. No strict spectral slack is assumed. -/
theorem theorem_11 :
  ∃ (P : RAMProgram) (C d : ℕ), Admissible P ∧ 0 < C ∧
    ∀ (n : ℕ), 0 < n → ∀ (J : Matrix (Fin n) (Fin n) ℝ), J.IsSymm →
    ∀ (h η : Fin n → ℝ), spectralWidth J * alpha (minField η) ≤ 1 →
    ∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
    ∀ q : Query n, SuccessfulRun P (goalBudget C d J h η ε δ) J h η ε δ q := by sorry
end TFIMPhaseDiagram.Classical
