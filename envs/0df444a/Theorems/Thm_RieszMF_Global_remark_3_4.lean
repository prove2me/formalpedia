-- Prove2me | Theorems.Thm_RieszMF_Global_remark_3_4
-- name    : RieszMF.Global.remark_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:11:58.277735+00:00
-- url     : https://prove2.me/theorems/2fe7a69d-970e-4a54-9320-69dd44b794ff
-- title:
--   Remark 3.4, p. 12 — the $L^p$ norms of solutions of (1.5) are nonincreasing in time
-- statement:
--   Let $d\ge3$, $0\le s<d-2$, $\sigma>0$, $\mathbb M$ with (1.2) and $\mathsf g$ admissible. Let $\mu\in C([0,\infty);L^1\cap L^\infty)$ be a mild solution of (1.5), nonnegative if $\mathbb M:\nabla^{\otimes2}\mathsf g$ does not vanish identically on $\mathbb R^d\setminus\{0\}$. Then for every $1\le p\le\infty$,
--
--   $$\|\mu^t\|_{L^p}\le\|\mu^{t'}\|_{L^p}\qquad\text{for all }0\le t'\le t.$$
--
--   In particular $\sup_t\|\mu^t\|_{L^\infty}=\|\mu^0\|_{L^\infty}$, which is how the constants of the main theorems depend on $\mu$ only through $\|\mu^0\|_{L^\infty}$.
--
--   **Formalization Note** The remark states no sign condition, but its argument (3.19) uses assumption (x) through $(\mathbb M:\nabla^{\otimes2}\mathsf g)*\mu^t\ge0$, which needs $\mu\ge0$ unless $\mathbb M:\nabla^{\otimes2}\mathsf g\equiv0$; the hypothesis of Proposition 3.8 is added for that reason. The remark is phrased on $[0,T]$; the statement is given on $[0,\infty)$ for every $T$ at once.
-- source:
--   Rosenzweig & Serfaty, Global-in-time mean-field convergence for singular Riesz-type diffusive flows, arXiv:2108.09878v1, p. 12, Remark 3.4

import Mathlib
import Definitions.Def_RieszMF_Global_Setting

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace RieszMF.Global

/-- Remark 3.4 (p. 12): for a solution `μ ∈ C([0, ∞); L¹ ∩ L^∞)` of (1.5) (nonnegative if
`𝕄 : ∇^{⊗2} g ≢ 0`, the hypothesis of Proposition 3.8) and `1 ≤ p ≤ ∞`, the norm `‖μ^t‖_{L^p}`
is nonincreasing in `t`. -/
theorem remark_3_4 :
    ∀ (d : ℕ) (s : ℝ), 3 ≤ d → 0 ≤ s → s < (d : ℝ) - 2 →
    ∀ (σ : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (g : RieszMF.Linear.E d → ℝ) (r₀ : ℝ),
      0 < σ → RieszMF.Linear.NegSemidef M → Admissible d s M g r₀ →
    ∀ (μ0 : RieszMF.Linear.E d → ℝ) (μ : ℝ≥0 → RieszMF.Linear.E d → ℝ),
      IsMildSolution d σ M g μ0 μ →
      ((∃ x : RieszMF.Linear.E d, x ≠ 0 ∧ RieszMF.Linear.frob M g x ≠ 0) → ∀ t, ∀ᵐ x ∂volume, 0 ≤ μ t x) →
    ∀ p : ℝ≥0∞, 1 ≤ p →
    ∀ t' t : ℝ≥0, t' ≤ t →
      eLpNorm (μ t) p volume ≤ eLpNorm (μ t') p volume := by sorry

end RieszMF.Global
