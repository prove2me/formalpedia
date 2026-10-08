-- Prove2me | Theorems.Thm_PiIrrationality_ZZEven_linearForm
-- name    : PiIrrationality.ZZEven.linearForm
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T09:46:15.890935+00:00
-- url     : https://prove2.me/theorems/cfd188d6-a3f4-4dda-9b44-9aca299bd150
-- title:
--   Even-index Zeilberger–Zudilin integrals are integer linear forms in $1$ and $\pi$
-- statement:
--   With $R_n$, $J_n$, $\mathrm{coef}_n$, $\Phi_n$ and $M_n$ as in the definition file `PiIrrationality_ZZEvenForms`, for every $n\ge1$ there are integers $U_n$ and $V_n$ with
--   $$
--   M_n\,J_n=U_n+V_n\pi,\qquad V_n=-\frac{M_n\,16^n\,\mathrm{coef}_n}{4}.
--   $$
--
--   This is the arithmetic of the Zeilberger–Zudilin construction at even index. The integrand has the even partial-fraction decomposition $R_n=P_n+\sum_{j=0}^{6n}c_{j,n}\bigl((5+t)^{-j-1}+(5-t)^{-j-1}\bigr)$ with $P_n\in\mathbb{Z}[t^2]$. Only the $j=0$ term produces $\pi$, through $\int(\tfrac1{5+t}+\tfrac1{5-t})\,dt=\pi i/2$. The multiplier $M_n=2^{4-5n}\operatorname{lcm}(1,\dots,8n)/\Phi_n$ clears all denominators: the $2$-adic and $5$-adic valuations of the Laurent coefficients give the power of $2$, and the deleted primes in $\Phi_n$ divide every relevant coefficient. The $\pi$-coefficient is $-M_nc_{0,n}/2$. The residue satisfies $c_{0,n}=16^n\,\mathrm{coef}_n/2$, by the substitution $z=(t+5)/(t-5)$, which turns $R_n(t)\,dt$ into $\tfrac12 16^n z^{-6n-1}S(z)^n\,dz$.
-- source:
--   Y. Bai, The irrationality measure of π is at most 7.101862832357, arXiv:2609.11276 (v2, 11 Sep 2026), Section 2: Lemmas 2.1–2.6 and Proposition 2.7 (with (a,b,c)=(2,4,6), so h=5 and d0=8), and equation (4.5); D. Zeilberger and W. Zudilin, The irrationality measure of π is at most 7.103205334137…, Moscow J. Combin. Number Theory 9 (2020), no. 4, 407–419, arXiv:1912.06345, Lemmas 1–6 and Proposition 1 at index 2n.

import Definitions.Def_PiIrrationality_ZZEvenForms
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

theorem PiIrrationality.ZZEven.linearForm (n : ℕ) (hn : 1 ≤ n) :
    ∃ U V : ℤ,
      (PiIrrationality.ZZEven.M n : ℂ) * PiIrrationality.ZZEven.J n =
          (U : ℂ) + (V : ℂ) * (Real.pi : ℂ) ∧
        (V : ℝ) = -(PiIrrationality.ZZEven.M n * 16 ^ n *
          (PiIrrationality.ZZEven.coef n : ℝ) / 4) := by
  sorry
