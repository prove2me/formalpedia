-- Prove2me | Theorems.Thm_TVSDP_PolyOpt_theorem_4
-- name    : TVSDP.PolyOpt.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:03.383438+00:00
-- url     : https://prove2.me/theorems/9f50ed0e-8b6a-40ba-b305-02f4d454d0b4
-- title:
--   Theorem 4, p. 11 — a strictly feasible TV-SDP has feasible polynomial solutions $x^k$ with $\langle c,x^k\rangle\to\mathrm{opt}$
-- statement:
--   Consider the time-varying semidefinite program
--
--   $$\mathrm{opt}=\sup_{x\in\mathbf L^n}\int_0^1\langle c(t),x(t)\rangle\,dt\quad\text{subject to}\quad \mathcal Fx(t)\succeq0\ \text{ for almost every } t\in[0,1],$$
--
--   with $\mathcal Fx(t)=A_0(t)+\sum_{i=1}^n x_i(t)A_i(t)+\sum_{i=1}^n\int_0^t x_i(s)D_i(t,s)\,ds$ and polynomial data $c$, $A_0,\dots,A_n$ (symmetric, in $t$) and $D_1,\dots,D_n$ (symmetric, in $(t,s)$). Suppose the program is strictly feasible: some $x^s\in\mathbf L^n$ and $\varepsilon>0$ satisfy $\mathcal Fx^s(t)\succeq\varepsilon I$ for almost every $t\in[0,1]$. Then there is a sequence of vectors of polynomials $p^k=(p^k_1,\dots,p^k_n)$ such that each polynomial solution $x^k(t)=p^k(t)$ is feasible and
--
--   $$\langle c,x^k\rangle_{\mathbf L^n}\longrightarrow\mathrm{opt}\qquad(k\to\infty).$$
--
--   In words, under strict feasibility, restricting a TV-SDP to polynomial solutions does not change its optimal value. Without strict feasibility this fails (Example 1 of the paper).
--
--   **Formalization Note** $\mathrm{opt}$ is an extended real and the limit is taken in $[-\infty,+\infty]$, so the case $\mathrm{opt}=+\infty$ is included. The data are polynomial, the paper's standing assumption (p. 3); the theorem is false for general bounded measurable data. The solutions $x^k$ are genuine polynomials on $[0,1]$, and feasibility is "almost every $t\in[0,1]$" with respect to Lebesgue measure on $[0,1]$.
-- source:
--   Ahmadi & El Khadir, Time-varying semidefinite programs, arXiv:1808.03994v2, p. 11, Theorem 4

import Mathlib
import Definitions.Def_TVSDP_PolyOpt_Setting

namespace TVSDP.PolyOpt

open Filter Topology

/-- Theorem 4, p. 11: if the TV-SDP (1) with polynomial data is strictly feasible, then there is a
sequence of feasible polynomial solutions `x^k` with `⟨c, x^k⟩_{L^n} → opt` as `k → ∞` (in `EReal`,
so `opt = +∞` is included). -/
theorem theorem_4 {n m : ℕ} (P : Data n m) (hP : StrictlyFeasible P) :
    ∃ p : ℕ → Fin n → Polynomial ℝ,
      (∀ k, Feasible P (polySol (p k))) ∧
      Tendsto (fun k => ((obj P (polySol (p k)) : ℝ) : EReal)) atTop (𝓝 (opt P)) := by sorry

end TVSDP.PolyOpt
