-- Prove2me | Theorems.Thm_SampleDrivenOS_Limit_b4_binomial_identity
-- name    : SampleDrivenOS.Limit.b4_binomial_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:19.873542+00:00
-- url     : https://prove2.me/theorems/d6c964dc-30ec-4ac7-a76e-cc765f8aa139
-- title:
--   B.4, p. 32 — $\sum_{\ell=1}^{j}\binom{j-1}{\ell-1}(1-t)^{j-\ell}t^\ell=t$
-- statement:
--   For every integer $j\ge1$ and every $t\in[0,1]$,
--   $$\sum_{\ell=1}^{j}\binom{j-1}{\ell-1}(1-t)^{j-\ell}t^{\ell}=t .$$
--
--   In the proof of Lemma 4 this identity turns the coefficient of $q(t,j)$ in $F_k(q)$, after $q(t,\ell)$ has been bounded below by $q(t,j)$, into the simple weight $t$.
-- source:
--   Correa, Cristi, Epstein & Soto, Sample-Driven Optimal Stopping: From the Secretary Problem to the i.i.d. Prophet Inequality, arXiv:2011.06516v2, p. 32, B.4 (proof of Lemma 4), last line

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology

namespace SampleDrivenOS.Limit

/-- B.4 (p. 32): for all `j ≥ 1` and `t ∈ [0, 1]`,
`∑_{ℓ=1}^{j} C(j-1, ℓ-1) (1-t)^{j-ℓ} t^ℓ = t`. -/
theorem b4_binomial_identity (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∑ ℓ ∈ Finset.Icc 1 j, ((j - 1).choose (ℓ - 1) : ℝ) * (1 - t) ^ (j - ℓ) * t ^ ℓ = t := by sorry

end SampleDrivenOS.Limit
