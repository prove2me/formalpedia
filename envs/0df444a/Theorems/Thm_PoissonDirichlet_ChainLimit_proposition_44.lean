-- Prove2me | Theorems.Thm_PoissonDirichlet_ChainLimit_proposition_44
-- name    : PoissonDirichlet.ChainLimit.proposition_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:57.512854+00:00
-- url     : https://prove2.me/theorems/b0ef2935-d092-4b39-8baf-25d091d138fe
-- title:
--   Proposition 44 (150): nY_n → (1 − α)/α almost surely
-- statement:
--   Let $0<\alpha<1$, $\theta> -\alpha$, and let $(V_n)\sim\mathrm{PD}(\alpha,\theta)$. For $n\ge1$, define the tail fraction $Y_n=V_n/(V_n+V_{n+1}+\cdots)$. Then almost surely,
--   $$nY_n\longrightarrow\frac{1-\alpha}{\alpha}\qquad(n\to\infty).$$
--   This is the almost-sure asymptotic scale of the ranked-frequency chain; in particular $Y_n$ is of order $1/n$.
--
--   **Formalization Note** The paper's index $n$ is `k+1` in Lean. The PD hypothesis refers to the ranked stick-breaking law of Definition 1; $Y_n$ is computed from the tail of that same sequence.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 891, Proposition 44, (150)

import Mathlib
import Definitions.Def_PoissonDirichlet_ChainLimit_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.ChainLimit

/-- Proposition 44 (150), p. 891: under `PD(α,θ)`, `n Yₙ → (1-α)/α`
almost surely. In this zero-based representation `n = k+1`. -/
theorem proposition_44 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (α θ : ℝ)
    (hα : 0 < α) (hα1 : α < 1) (hθ : -α < θ)
    (V : Ω → ℕ → ℝ) (hV : HasPD α θ P V) :
    ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => ((k : ℝ) + 1) * Yseq (V ω) k)
        atTop (𝓝 ((1 - α) / α)) := by sorry

end PoissonDirichlet.ChainLimit
