-- Prove2me | Theorems.Thm_TierneyMH_Mixture_proposition1_canonical_split
-- name    : TierneyMH.Mixture.proposition1_canonical_split
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T02:36:41.51637+00:00
-- url     : https://prove2.me/theorems/20bb8939-07a0-4701-b82e-b0dea202c870
-- title:
--   Proposition 1 via its proof: $R=\{h(x,y)>0,h(y,x)>0\}$ and $r=h(x,y)/h(y,x)$ satisfy Proposition 1 for $\pi(dx)Q(x,dy)$
-- statement:
--   Let $\pi$ be a probability measure on $(E,\mathcal E)$, let $Q$ be a Markov kernel on $E$, and let $\mu(dx,dy)=\pi(dx)Q(x,dy)$, $\mu^T(dx,dy)=\mu(dy,dx)$. Let $h=d\mu/d(\mu+\mu^T)$,
--
--   $$R=\{(x,y): h(x,y)>0\text{ and } h(y,x)>0\},\qquad r(x,y)=\begin{cases}h(x,y)/h(y,x), & (x,y)\in R,\\ 1,&(x,y)\notin R.\end{cases}$$
--
--   Then:
--
--   1. $R\in\mathcal E\otimes\mathcal E$ is symmetric, $\mu$ and $\mu^T$ are mutually absolutely continuous on $R$ and mutually singular on $R^c$;
--   2. $r$ is a measurable version of the density $d\mu_R/d\mu^T_R$ with $0<r(x,y)<\infty$ and $r(x,y)=1/r(y,x)$ for all $x,y\in E$.
--
--   This is the construction in the proof of Proposition 1, specialized to the measure $\mu=\pi\otimes Q$ of a Metropolis–Hastings algorithm. It certifies that the set and ratio from which $\alpha_{MH}$ is built are the paper's $R$ and $r$.
--
--   **Formalization Note** The ratio is set to $1$ also on the $(\mu+\mu^T)$-null subset of $R$ where $h$ is infinite, so that condition 2 holds at every point (see `canonRatio`). The paper states Proposition 1 for every $\sigma$-finite $\mu$; here $\mu$ is the finite measure $\pi\otimes Q$, the only case the mission uses.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 2, Proposition 1 and its proof

import Mathlib
import Definitions.Def_TierneyMH_Shared_IsSymmetricSplit
import Definitions.Def_TierneyMH_Shared_IsRatioVersion
import Definitions.Def_TierneyMH_Mixture_canonR
import Definitions.Def_TierneyMH_Mixture_canonRatio

open TierneyMH.Shared

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TierneyMH.Mixture

/-- **Proposition 1, via its proof** (Tierney 1998, p. 2), for `μ(dx, dy) = π(dx) Q(x, dy)`.
With `ν = μ + μᵀ`, `h = dμ/dν`, `R = {(x, y) : h(x, y) > 0 and h(y, x) > 0}` (`canonR π Q`)
and `r = h(x, y)/h(y, x)` on `R`, `r = 1` on `Rᶜ` (`canonRatio π Q`):
`R` is a symmetric measurable set on which `μ` and `μᵀ` are mutually absolutely continuous and
off which they are mutually singular, and `r` is a version of `dμ_R/dμᵀ_R` with
`0 < r < ∞` and `r(x, y) = 1/r(y, x)` everywhere. -/
theorem proposition1_canonical_split {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (Q : Kernel E E) [IsMarkovKernel Q] :
    IsSymmetricSplit (π ⊗ₘ Q) (canonR π Q) ∧
      IsRatioVersion (π ⊗ₘ Q) (canonR π Q) (canonRatio π Q) := by sorry

end TierneyMH.Mixture
