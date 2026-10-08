-- Prove2me | Theorems.Thm_PoissonDirichlet_Moments_proposition_26
-- name    : PoissonDirichlet.Moments.proposition_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:03.337606+00:00
-- url     : https://prove2.me/theorems/caa96045-3847-4153-83f3-3d83d794b33c
-- title:
--   Proposition 26, p. 871 — conditional Wendel formula (68) for exp(−λ/V_n) given R_1, …, R_{n−1}, X_n
-- statement:
--   Let $0<\alpha<1$ and let $(V_n)$ have the $\mathrm{PD}(\alpha,0)$ law. Let $L=\lim_{n\to\infty}nV_n^\alpha$ be the local time (24), $X_n=LV_n^{-\alpha}$ (27), $R_n=V_{n+1}/V_n$ (21) and $A_n=(V_1+\dots+V_n)/V_{n+1}$ with $A_0=0$ (31). For $n\ge1$ and $\lambda\ge0$,
--
--   $$E\Big[\exp\Big(-\frac{\lambda}{V_n}\Big)\,\Big|\,R_1,\dots,R_{n-1},X_n\Big]=\exp\big(-\lambda(1+A_{n-1})\big)\exp\big[-X_n(\psi_\alpha(\lambda)-1)\big],$$
--
--   with $\psi_\alpha$ as in (34).
--
--   This conditional form of Wendel's formula is the second step of the proof of Lemma 27: it reduces $E[\exp(-t/V_n)\mid X_n]$ to the law of $A_{n-1}$.
--
--   **Formalization Note** The conditional expectation is stated through its defining property: for every nonnegative measurable function $g$ of $(R_1,\dots,R_{n-1},X_n)$, the expectations of $\exp(-\lambda/V_n)\,g(\cdot)$ and of the right-hand side times $g(\cdot)$ agree (as lower integrals). Indexing is from $0$: the Lean index $k$ is $n-1$. $L$ enters only through its defining limit (24), assumed almost surely; Proposition 10 (i) of the paper is that such an $L$ exists. The paper proves this result via a Poisson random measure representation.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 871, Proposition 26, (68)

import Mathlib
import Definitions.Def_PoissonDirichlet_Moments_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Moments

/-- Proposition 26, p. 871, (68), 0-based (`k = n - 1`): under `PD(α, 0)`, with `L` the local
time (24) and `X_n = L V_n^{-α}` (27),
`E[exp(-λ/V_n) | R_1, …, R_{n-1}, X_n] = exp(-λ(1 + A_{n-1})) exp(-X_n(ψ_α(λ) - 1))`.
The conditional expectation is stated through its defining property: the identity holds after
multiplying by `g(R_1, …, R_{n-1}, X_n)` and integrating, for every nonnegative measurable `g`. -/
theorem proposition_26 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V ω k ^ α) atTop (𝓝 (L ω)))
    (k : ℕ) (l : ℝ) (hl : 0 ≤ l) :
    ∀ g : (Fin k → ℝ) × ℝ → ENNReal, Measurable g →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-l / V ω k)) *
          g (fun i : Fin k => PoissonDirichlet.Ratio.ratio (V ω) i, Xseq α (L ω) (V ω) k) ∂P =
        ∫⁻ ω, ENNReal.ofReal (Real.exp (-l * (1 + PoissonDirichlet.Wendel.Aseq (V ω) k)) *
              Real.exp (-(Xseq α (L ω) (V ω) k) * (PoissonDirichlet.Wendel.psi α l - 1))) *
          g (fun i : Fin k => PoissonDirichlet.Ratio.ratio (V ω) i, Xseq α (L ω) (V ω) k) ∂P := by sorry

end PoissonDirichlet.Moments
