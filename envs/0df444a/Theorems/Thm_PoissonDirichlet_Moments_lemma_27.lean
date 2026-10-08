-- Prove2me | Theorems.Thm_PoissonDirichlet_Moments_lemma_27
-- name    : PoissonDirichlet.Moments.lemma_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:50.547487+00:00
-- url     : https://prove2.me/theorems/7088b163-7ae3-423d-9ca0-5c0692ecf57b
-- title:
--   Lemma 27, p. 874 — joint moments E[L^ℓ V_n^p] under PD(α, 0), (85)
-- statement:
--   Let $0<\alpha<1$, let $(V_n)$ have the $\mathrm{PD}(\alpha,0)$ law and let $L=\lim_n nV_n^\alpha$ be its local time (24). For all real $\ell>-1$ and $p>0$ with $p+\ell\alpha>0$, and every $n\ge1$,
--
--   $$E\big[L^\ell V_n^p\big]=\frac{\Gamma(\ell+n)}{\Gamma(n)\Gamma(p+\ell\alpha)}\int_0^\infty t^{p+\ell\alpha-1}e^{-t}\phi_\alpha(t)^{n-1}\psi_\alpha(t)^{-\ell-n}\,dt,$$
--
--   with $\phi_\alpha,\psi_\alpha$ as in (33)–(34).
--
--   Together with the change of measure of Proposition 14 (take $\ell=\theta/\alpha$) this gives the moment formula of Proposition 17 for $\mathrm{PD}(\alpha,\theta)$.
--
--   **Formalization Note** The hypothesis $p+\ell\alpha>0$ is not printed in the paper; it is necessary. When $\ell\ge0$ it follows from $p>0$. When $-1<\ell<0$ and $p+\ell\alpha\le0$ the left side is finite while the $t$-integral diverges at $0$ (the integrand behaves like $t^{p+\ell\alpha-1}$) and $\Gamma(p+\ell\alpha)$ is at a pole or of the wrong sign; the paper's proof applies (86) with exponent $p+\ell\alpha$, which needs it positive. The expectation is a lower integral of a nonnegative function, compared with the nonnegative real right-hand side. Indexing is from $0$: the Lean index $k$ is $n-1$.
-- source:
--   Pitman and Yor, The two-parameter Poisson–Dirichlet distribution derived from a stable subordinator, Ann. Probab. 25 (1997), p. 874, Lemma 27, (85)

import Mathlib
import Definitions.Def_PoissonDirichlet_Moments_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace PoissonDirichlet.Moments

/-- Lemma 27, p. 874, (85), 0-based (`n = k + 1`): under `PD(α, 0)`, with `L = lim n V_n^α`
(24), for real `ℓ > -1`, `p > 0` (and `p + ℓα > 0`, a disclosed necessary addition),
`E[L^ℓ V_n^p] = Γ(ℓ + n)/(Γ(n)Γ(p + ℓα)) ∫_0^∞ t^{p+ℓα-1} e^{-t} φ_α(t)^{n-1} ψ_α(t)^{-ℓ-n} dt`.
The expectation is a lintegral in `[0, ∞]`. -/
theorem lemma_27 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (V : Ω → ℕ → ℝ) (hV : PoissonDirichlet.Ratio.HasPD α 0 P V) (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun k : ℕ => ((k : ℝ) + 1) * V ω k ^ α) atTop (𝓝 (L ω)))
    (ℓ : ℝ) (hℓ : -1 < ℓ) (p : ℝ) (hp : 0 < p) (hpℓ : 0 < p + ℓ * α) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (L ω ^ ℓ * V ω k ^ p) ∂P =
      ENNReal.ofReal
        (Real.Gamma (ℓ + ((k : ℝ) + 1)) / (Real.Gamma ((k : ℝ) + 1) * Real.Gamma (p + ℓ * α)) *
          ∫ t in Set.Ioi (0 : ℝ), t ^ (p + ℓ * α - 1) * Real.exp (-t) * PoissonDirichlet.Wendel.phi α t ^ k *
            PoissonDirichlet.Wendel.psi α t ^ (-ℓ - ((k : ℝ) + 1))) := by sorry

end PoissonDirichlet.Moments
