-- Prove2me | Theorems.Thm_PeskirShiryaev_AmericanPut_optimal_hitting
-- name    : PeskirShiryaev.AmericanPut.optimal_hitting
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:27:21.616977+00:00
-- url     : https://prove2.me/theorems/9ab8b86e-6a7b-4241-a601-1d4735aa1436
-- title:
--   Eqs. (25.2.23)–(25.2.25) — optimal hitting and boundary regularity
-- statement:
--   For the geometric Brownian American put with positive $r,\sigma,K,T$, the boundary $b$ extracted from the value function is continuous and nondecreasing on $[0,T]$, takes values in $(0,K]$, and has $b(T)=K$. Before maturity it lies strictly below $K$ and identifies the stopping set:
--   $$V(t,x)=G(x)\quad\Longleftrightarrow\quad x\le b(t),\qquad 0\le t<T,\ x>0.$$
--   For every $t\in[0,T]$ and $x>0$, the hitting time
--   $$\tau_b=\inf\{0\le s\le T-t:X_s^x\le b(t+s)\}$$
--   is admissible and attains $V(t,x)=E[e^{-r\tau_b}G(X_{\tau_b}^x)]$, with infimum of the empty set equal to $T-t$.
--
--   The theorem connects the operational stopping problem to its moving exercise boundary.
--
--   **Formalization Note** The stopping-set characterization is stated only before maturity; at maturity every state has value equal to payoff. The threshold itself remains $K$. Continuity, monotonicity, and optimality are conclusions, not assumptions.
-- source:
--   Peskir and Shiryaev, Optimal Stopping and Free-Boundary Problems, Birkhäuser Verlag, 2006, DOI 10.1007/978-3-7643-7390-0, pp. 380, 383 (PDF 396, 399), Eqs. (25.2.8)–(25.2.9), (25.2.23)–(25.2.25)

import Definitions.Def_PeskirShiryaev_AmericanPut_Boundary

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace PeskirShiryaev.AmericanPut

theorem optimal_hitting {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) :
    ContinuousOn M.boundary (Set.Icc 0 M.T) ∧
    MonotoneOn M.boundary (Set.Icc 0 M.T) ∧
    (∀ t ∈ Set.Icc 0 M.T, 0 < M.boundary t ∧ M.boundary t ≤ M.K) ∧
    M.boundary M.T = M.K ∧
    (∀ t ∈ Set.Ico 0 M.T, M.boundary t < M.K ∧
      ∀ x : ℝ, 0 < x → (M.value t x = M.payoff x ↔ x ≤ M.boundary t)) ∧
    ∀ t ∈ Set.Icc 0 M.T, ∀ x : ℝ, 0 < x →
      M.Admissible t (M.hit M.boundary t x) ∧
      M.reward x (M.hit M.boundary t x) = M.value t x := by sorry

end PeskirShiryaev.AmericanPut
