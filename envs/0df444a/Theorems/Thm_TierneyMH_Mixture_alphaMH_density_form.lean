-- Prove2me | Theorems.Thm_TierneyMH_Mixture_alphaMH_density_form
-- name    : TierneyMH.Mixture.alphaMH_density_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T03:07:54.691612+00:00
-- url     : https://prove2.me/theorems/e7cc2ddc-7fd4-4b06-bf4d-e46caedef624
-- title:
--   $\pi(dx)Q(x,dy)\alpha_{MH}(x,y)=\min\{h(y,x),h(x,y)\}\,\nu(dx,dy)$ for any symmetric dominating $\nu$
-- statement:
--   Let $\pi$ be a probability measure and $Q$ a Markov proposal kernel on $E$, and let $\mu(dx,dy)=\pi(dx)Q(x,dy)$. Let $\nu$ be any $\sigma$-finite measure on $E\times E$ that is symmetric, $\nu(dx,dy)=\nu(dy,dx)$, and dominates $\mu$, and let $h=d\mu/d\nu$. Then, as measures on $E\times E$,
--
--   $$\pi(dx)\,Q(x,dy)\,\alpha_{MH}(x,y) = \min\{h(y,x),\,h(x,y)\}\,\nu(dx,dy).$$
--
--   This is the first step of the proof of Proposition 5, where it is applied to the mixture proposal: the part of the joint law of a move that is accepted has density $\min\{h(y,x),h(x,y)\}$ with respect to every symmetric dominating measure, not only the one used to define $\alpha_{MH}$.
--
--   **Formalization Note** The page writes the first equality as $h(x,y)\min\{h(y,x)/h(x,y),1\}\,\nu(dx,dy)$ for the mixture $Q=\sum_i\beta_iQ_i$; the statement gives the resulting min form, for an arbitrary Markov proposal kernel. $\alpha_{MH}$ is defined through the specific measure $\mu+\mu^T$; the theorem relates it to an arbitrary symmetric dominating $\nu$.
-- source:
--   L. Tierney, A Note on Metropolis–Hastings Kernels for General State Spaces, Ann. Appl. Probab. 8(1) (1998) 1–9, DOI 10.1214/aoap/1027961031, p. 8, proof of Proposition 5 (first two lines of the display)

import Mathlib
import Definitions.Def_TierneyMH_Mixture_alphaMH

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TierneyMH.Mixture

/-- **Density form of `μ α_MH`** (Tierney 1998, proof of Proposition 5, p. 8, first two lines
of the display). Let `ν` be any σ-finite symmetric measure on `E × E` (`ν(dx, dy) = ν(dy, dx)`)
dominating `μ(dx, dy) = π(dx) Q(x, dy)`, and let `h = dμ/dν`. Then
`π(dx) Q(x, dy) α_MH(x, y) = min{h(y, x), h(x, y)} ν(dx, dy)`
as measures on `E × E`. -/
theorem alphaMH_density_form {E : Type*} [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (Q : Kernel E E) [IsMarkovKernel Q]
    (ν : Measure (E × E)) [SigmaFinite ν] (hν_symm : ν.map Prod.swap = ν)
    (hμν : π ⊗ₘ Q ≪ ν) :
    (π ⊗ₘ Q).withDensity (alphaMH π Q) =
      ν.withDensity (fun p => min ((π ⊗ₘ Q).rnDeriv ν p.swap) ((π ⊗ₘ Q).rnDeriv ν p)) := by sorry

end TierneyMH.Mixture
