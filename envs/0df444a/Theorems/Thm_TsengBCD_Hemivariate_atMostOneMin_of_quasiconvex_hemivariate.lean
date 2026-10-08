-- Prove2me | Theorems.Thm_TsengBCD_Hemivariate_atMostOneMin_of_quasiconvex_hemivariate
-- name    : TsengBCD.Hemivariate.atMostOneMin_of_quasiconvex_hemivariate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T23:06:51.530978+00:00
-- url     : https://prove2.me/theorems/254ec372-d665-4b08-b74c-0e53935f57e7
-- title:
--   Remark after Theorem 4.1, p. 483 — a quasiconvex hemivariate function has at most one minimum point
-- statement:
--   Let $h:V\to[-\infty,\infty]$ be a function on a real vector space that is quasiconvex,
--   $$h(x+\lambda d)\le\max\{h(x),h(x+d)\}\quad\text{for all }x,d\text{ and }\lambda\in[0,1],$$
--   and hemivariate (not constant on any nondegenerate line segment contained in $\operatorname{dom}h$). Then $h$ has at most one minimum point: if $a$ and $b$ both minimize $h$ over $V$ and $h(a)<\infty$, then $a=b$.
--
--   Applied to the section $x_k\mapsto f(x_1,\dots,x_N)$, this is the page's remark that if $f$ is quasiconvex and hemivariate in $x_k$, then $f$ has at most one minimum in $x_k$; it links Assumption B2 to the uniqueness hypothesis of Theorem 4.1(c).
--
--   **Formalization Note.** A minimum point is a point of $\operatorname{dom}h$ attaining the infimum, so the case $h\equiv\infty$ (where every point attains the infimum) is excluded by $h(a)<\infty$.
-- source:
--   Tseng, Convergence of a block coordinate descent method for nondifferentiable minimization, J. Optim. Theory Appl. 109 (2001), p. 483, remark after Theorem 4.1

import Mathlib
import Definitions.Def_TsengBCD_Hemivariate_Setting

namespace TsengBCD.Hemivariate

open Filter Topology

theorem atMostOneMin_of_quasiconvex_hemivariate {V : Type*} [AddCommGroup V] [Module ℝ V]
    (h : V → EReal) (hqc : IsQuasiconvex h) (hhv : IsHemivariate h) :
    ∀ a b : V, h a ≠ ⊤ → (∀ c, h a ≤ h c) → (∀ c, h b ≤ h c) → a = b := by sorry

end TsengBCD.Hemivariate
