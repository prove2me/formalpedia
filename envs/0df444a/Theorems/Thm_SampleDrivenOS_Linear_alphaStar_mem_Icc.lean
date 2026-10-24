-- Prove2me | Theorems.Thm_SampleDrivenOS_Linear_alphaStar_mem_Icc
-- name    : SampleDrivenOS.Linear.alphaStar_mem_Icc
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-23T13:48:06.94871+00:00
-- url     : https://prove2.me/theorems/97168989-22f2-4e87-9d66-5f9670917ba8
-- title:
--   B.9, p. 37 — the i.i.d. prophet constant satisfies $\alpha^*\in[0.74,0.75]$
-- statement:
--   Let $\alpha^*\in(0,1)$ be a solution of
--   $$\int_0^1 \frac{dy}{y(1-\ln y)+\frac{1}{\alpha^*}-1}=1 .$$
--   Then
--   $$0.74\le \alpha^*\le 0.75 .$$
--
--   This is the numerical fact "$\alpha^*\approx 0.745$" used at the end of the proof of Theorem 9 (Appendix B.9, p. 37): it places $\alpha^*$ in the interval $[0.74,0.75]$ on which the numerical bound of B.9 (the term $\bigl(\tfrac{1}{p\alpha^*}-\tfrac1e\bigr)\ln\bigl(\cdots\bigr)\ge 0.8$) is stated. The constant $\alpha^*\approx 0.7454$ is the optimal i.i.d. prophet-inequality constant (Hill--Kertz, Kertz, Correa et al.), so the bound is reusable wherever $\alpha^*$ (or $\beta^*=1/\alpha^*$) enters a numerical argument.
--
--   **Formalization Note** $\alpha^*$ enters through the predicate `SampleDrivenOS.Limit.IsAlphaStar s`, which asserts $0<s<1$ and that the interval integral above equals $1$ (with Lean's convention $\ln 0=0$ at the single point $y=0$). The statement holds for every such $s$; existence and uniqueness are not assumed.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, Appendix B.9 (proof of Theorem 9), p. 37: "since we know that α* ≈ 0.745"; α* defined on p. 17 (before Theorem 8)

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

namespace SampleDrivenOS.Linear

theorem alphaStar_mem_Icc (s : ℝ) (hs : SampleDrivenOS.Limit.IsAlphaStar s) :
    s ∈ Set.Icc (0.74 : ℝ) 0.75 := by sorry

end SampleDrivenOS.Linear
