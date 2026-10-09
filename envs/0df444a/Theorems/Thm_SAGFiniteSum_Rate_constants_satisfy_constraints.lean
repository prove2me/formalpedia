-- Prove2me | Theorems.Thm_SAGFiniteSum_Rate_constants_satisfy_constraints
-- name    : SAGFiniteSum.Rate.constants_satisfy_constraints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:20:51.767982+00:00
-- url     : https://prove2.me/theorems/7595ce27-b113-4611-8bf4-0388a953334e
-- title:
--   App. B.5–B.6, pp. 42–46 — the B.5 constants satisfy Constraints 1–9 for n ≥ 2, 0 ≤ μ ≤ L
-- statement:
--   Let $n\ge2$, $L>0$ and $0\le\mu\le L$, and take the constants of App. B.5:
--   $$
--   \alpha=\tfrac1{16L},\ a_1=\tfrac1{32nL}\big(1-\tfrac1{2n}\big),\ a_2=\tfrac1{16nL}\big(1-\tfrac1{2n}\big),\ b=-\tfrac1{4n}\big(1-\tfrac1n\big),\ c=\tfrac{4L}n,\ h=\tfrac12-\tfrac1n,\ d=\tfrac\alpha n,\ \delta=\min\big(\tfrac1{8n},\tfrac\mu{16L}\big),
--   $$
--   $\gamma=1$ and $C_3=\frac1{32n}$, and let $B_3,B_4,C_0,C_1,C_2$ be the coefficients of App. B.3 and $D=na_1+a_2+n\mu d^2$. Then Constraints 1–9 of p. 42 hold:
--   $$
--   h\ge0,\quad 2h-\gamma\le0,\quad B_3>0,\quad B_4>0,\quad D\ge0,\quad \tfrac L2(2h-\gamma)+c-\tfrac nD(dL+b)^2\ge0,
--   $$
--   $$
--   C_2\le0,\quad C_1+C_3\le0,\quad C_0+\mu(C_1+C_3)+\mu^2C_2\le0 .
--   $$
--
--   This is the verification step of the proof: with these constraints, the B.3 bound yields the decrease of the Lyapunov function and B.4 its domination of $g-g(x^*)$.
--
--   **Formalization Note** A pure real-arithmetic statement. $n\ge2$ is the page's "We will assume $n>1$" (p. 43). $\mu\le L$ is B.6's "without loss of generality, we may assume $L=1$ and $\mu\in[0,1]$". $B_4$ is as defined on p. 40, including the term $-(1-\delta)\mu hd^2$ that B.6 discards in its computation. The page's own check is symbolic computation plus an off-paper Matlab script for $n\in\{2,3,4\}$.
-- source:
--   Schmidt, Le Roux & Bach, arXiv:1309.2388v2, App. B.5 (Constraints 1–9, p. 42; constants, p. 43) and B.6 (pp. 43–46)

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model
import Definitions.Def_SAGFiniteSum_Rate_Lyapunov

open scoped RealInnerProductSpace

namespace SAGFiniteSum.Rate

/-- B.5–B.6 (arXiv:1309.2388v2, pp. 42–46). For `n ≥ 2`, `L > 0` and `0 ≤ μ ≤ L`, the B.5
parameters (`α = 1/(16L)`, `a₁`, `a₂`, `b`, `c`, `d = α/n`, `h`, `δ = min(1/(8n), μ/(16L))`),
with `γ = 1` and `C₃ = 1/(32n)`, satisfy Constraints 1–9 of p. 42. -/
theorem constants_satisfy_constraints (n : ℕ) (hn : 2 ≤ n) (L μ : ℝ) (hL : 0 < L)
    (hμ : 0 ≤ μ) (hμL : μ ≤ L) :
    let P := sagParams n L μ
    let D := (n : ℝ) * P.a1 + P.a2 + (n : ℝ) * μ * P.d ^ 2
    0 ≤ P.h
    ∧ 2 * P.h - 1 ≤ 0
    ∧ 0 < coefB3 n L P
    ∧ 0 < coefB4 n L μ P
    ∧ 0 ≤ D
    ∧ 0 ≤ L / 2 * (2 * P.h - 1) + P.c - (n : ℝ) / D * (P.d * L + P.b) ^ 2
    ∧ coefC2 n L μ P ≤ 0
    ∧ coefC1 n L μ P + sagC3 n ≤ 0
    ∧ coefC0 n L μ P + μ * (coefC1 n L μ P + sagC3 n) + μ ^ 2 * coefC2 n L μ P ≤ 0 := by sorry

end SAGFiniteSum.Rate
