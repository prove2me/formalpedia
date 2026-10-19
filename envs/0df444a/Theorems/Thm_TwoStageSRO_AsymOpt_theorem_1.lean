-- Prove2me | Theorems.Thm_TwoStageSRO_AsymOpt_theorem_1
-- name    : TwoStageSRO.AsymOpt.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:09:23.923684+00:00
-- url     : https://prove2.me/theorems/550da476-946b-4140-a9cb-251681f60730
-- title:
--   Theorem 1, p. 10 — v̂^SRO_N ≤ v̂^MP_N ≤ v̂^SP_N and V̂^SRO_N(x) ≤ V̂^MP_N(x) ≤ V̂^SP_N(x)
-- statement:
--   Fix a policy class $\Pi$ of functions $\mathbb R^d\to\mathbb R^r$, an $\ell_p$-norm, a radius $\epsilon_N$, data $\xi^1,\dots,\xi^N$, and consider the sample robust problem (SRO), its single-policy approximation (SP) and its multi-policy approximation (MP), with $\hat V^{SP}_N(x)$ and $\hat V^{MP}_N(x)$ equal to $+\infty$ when $x$ admits no feasible policies. Then
--   $$\hat v^{SRO}_N\le\hat v^{MP}_N\le\hat v^{SP}_N\qquad\text{and}\qquad \hat V^{SRO}_N(x)\le\hat V^{MP}_N(x)\le\hat V^{SP}_N(x)\ \text{ for all } x\in\mathbb R^n.$$
--
--   The multi-policy approximation is thus a valid upper approximation of (SRO), never worse than the single-policy one, although its $N$ policies may prescribe contradicting recourse decisions on overlapping uncertainty sets.
--
--   **Formalization Note** Stated for every policy class, every radius $\epsilon\in\mathbb R$, every sample path and every $N$ (including $N=0$, where all objectives reduce to $c^\top x$ or $+\infty$). All values are in `EReal`.
-- source:
--   Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 10, Theorem 1

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_TwoStageSRO_AsymOpt_Model
import Definitions.Def_TwoStageSRO_AsymOpt_SampleProblems

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped ENNReal

namespace TwoStageSRO.AsymOpt

/-- Bertsimas, Shtern, Sturt, Two-Stage Sample Robust Optimization, arXiv:1907.07142v4, p. 10, Theorem 1:
`v̂^SRO_N ≤ v̂^MP_N ≤ v̂^SP_N` and `V̂^SRO_N(x) ≤ V̂^MP_N(x) ≤ V̂^SP_N(x)` for all `x ∈ ℝⁿ`.

**Formalization Note** Stated for every policy class `PiC ⊆ R^{d,r}` (the paper's `Π`, §3.2), every
`ℓp`-norm, every radius `ε`, every sample path `s` and every `N`. `V̂^SP_N` and `V̂^MP_N` are `+∞`
at first-stage decisions without feasible policies (p. 10). -/
theorem theorem_1 {n d r m mt : ℕ} (M : Model n d r m mt) (PiC : Set (Pol d r))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (ε : ℝ) (s : ℕ → Fin d → ℝ) (N : ℕ) :
    (vSRO M p ε s N ≤ vMP M PiC p ε s N ∧ vMP M PiC p ε s N ≤ vSP M PiC p ε s N) ∧
    ∀ x : Fin n → ℝ,
      VSRO M p ε s N x ≤ VMP M PiC p ε s N x ∧ VMP M PiC p ε s N x ≤ VSP M PiC p ε s N x := by sorry

end TwoStageSRO.AsymOpt
