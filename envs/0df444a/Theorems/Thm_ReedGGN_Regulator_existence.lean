-- Prove2me | Theorems.Thm_ReedGGN_Regulator_existence
-- name    : ReedGGN.Regulator.existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:45.257339+00:00
-- url     : https://prove2.me/theorems/a565bc8e-2d39-4ee4-9b6c-3a873faa47fd
-- title:
--   Proof of Proposition 3.1, Existence — the successive approximations (A.3) converge uniformly on bounded intervals to a càdlàg solution of (3.1)
-- statement:
--   Let $B$, $\mu$, $a$, $\delta>0$ and $0<\varepsilon<1$ be as in the uniqueness milestone: $B(y+\delta)-B(y)<\varepsilon$ for all $y\ge0$ and $\mu([0,\delta])<\varepsilon$. Let $x$ be càdlàg and let $(u_n)$ be the successive approximations (A.3):
--   $$u_0\equiv0,\qquad u_{n+1}(t)=x(t)+\int_{[0,t]}(u_n(t-s)+a)^+\,dB(s),\quad t\ge0 .$$
--   Then there is a càdlàg path $u^\star$ such that $\|u_n-u^\star\|_T\to0$ as $n\to\infty$ for every $T\ge0$, and $u^\star$ solves (3.1).
--
--   This is the existence half of Proposition 3.1 in the non-degenerate case, by the method of successive approximations.
--
--   **Formalization Note** The paper writes (A.3) "for $n\ge1$"; the recursion starts at $n=0$. The paper's limit is taken "under the supremum metric $u$", i.e. uniformly on every bounded interval $[0,T]$, which is what is stated.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, pp. 32–34, proof of Proposition 3.1 (Existence), Eq. (A.3)

import Mathlib
import Definitions.Def_ReedGGN_Regulator_PathSpace
import Definitions.Def_ReedGGN_Regulator_Equation

namespace ReedGGN.Regulator

open MeasureTheory Filter Topology

/-- Proof of Proposition 3.1, Existence (pp. 32–34): under the window condition of the
non-degenerate case, for every càdlàg input `x` the successive approximations (A.3),
`u_0 = 0`, `u_{n+1} = x + Ψ^a_B(u_n)`, converge uniformly on every `[0, T]` to a càdlàg
path `u⋆`, and `u⋆` solves (3.1). -/
theorem existence (μ : Measure ℝ) [IsProbabilityMeasure μ] (a δ ε : ℝ)
    (hδ : 0 < δ) (hε₀ : 0 < ε) (hε₁ : ε < 1)
    (hB₀ : μ (Set.Icc 0 δ) < ENNReal.ofReal ε)
    (hB : ∀ y, 0 ≤ y → μ (Set.Ioc y (y + δ)) < ENNReal.ofReal ε)
    (x : ℝ → ℝ) (hx : IsCadlag x) :
    ∃ uStar : ℝ → ℝ, IsCadlag uStar ∧
      (∀ T, 0 ≤ T → Tendsto (fun n => supNorm T (picard μ a x n - uStar)) atTop (𝓝 0)) ∧
      SolvesRegulator μ a x uStar := by sorry

end ReedGGN.Regulator
