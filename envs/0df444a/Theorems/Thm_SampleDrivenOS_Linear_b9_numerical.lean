-- Prove2me | Theorems.Thm_SampleDrivenOS_Linear_b9_numerical
-- name    : SampleDrivenOS.Linear.b9_numerical
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:28.088992+00:00
-- url     : https://prove2.me/theorems/b48e9446-9cad-4258-871f-7ea08e14e378
-- title:
--   B.9, p. 37 — for $\alpha^*\in[0.74,0.75]$ and $p\in(0,1)$ the log term is at least $0.8$
-- statement:
--   For every $s\in[0.74,\,0.75]$ and every $p\in(0,1)$,
--   $$\Bigl(\frac1{ps}-\frac1e\Bigr)\ln\left(\frac{\tfrac1{ps}+\tfrac pe}{\tfrac1{ps}+\tfrac pe-1}\right)\ge 0.8 .$$
--
--   The paper states this as a numerical check, for any value $\alpha^*=s$ in the interval $[0.74,0.75]$. Combined with the integral bound it gives the final upper bound on $c(p)$.
--
--   **Formalization Note** The claim is quantified over the whole interval $s\in[0.74,0.75]$, as printed, not only over $\alpha^*$. $e=\exp 1$. For $s,p$ in this range $1/(ps)>1$, so every division and the logarithm's argument (which exceeds $1$) are well defined.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 37, B.9 (Proof of Theorem 9), sentence after the first display

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting

namespace SampleDrivenOS.Linear

theorem b9_numerical (s : ℝ) (hs : s ∈ Set.Icc (0.74 : ℝ) 0.75) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (0.8 : ℝ) ≤ (1 / (p * s) - 1 / Real.exp 1) *
      Real.log ((1 / (p * s) + p / Real.exp 1) / (1 / (p * s) + p / Real.exp 1 - 1)) := by sorry

end SampleDrivenOS.Linear
