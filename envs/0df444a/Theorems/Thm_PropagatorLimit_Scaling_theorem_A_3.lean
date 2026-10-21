-- Prove2me | Theorems.Thm_PropagatorLimit_Scaling_theorem_A_3
-- name    : PropagatorLimit.Scaling.theorem_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:25.924488+00:00
-- url     : https://prove2.me/theorems/0be0c043-ba3e-47d2-b078-f53cd4a7e010
-- title:
--   Theorem A.3, p. 25 — functional CLT: normalized sums of F(t, ΔX/√Δt) converge stably in law
-- statement:
--   Let $(W,W^\perp)$ be a Brownian pair on a filtered probability space and let $X$ satisfy Assumption A.1:
--   $$dX_t=b_t\,dt+\sigma_t\,dW_t,\qquad d\sigma_t=\tilde b_t\,dt+\tilde\sigma_t\,dW_t+a_t\,dW^\perp_t,$$
--   with locally bounded $b,\tilde b,\tilde\sigma,a$. Let $T>0$, and let $F:[0,T]\times\mathbb R\to\mathbb R$ satisfy Assumption A.2 for a function $G$ of at most linear growth and a constant $\gamma>1/2$. Write $\tilde E$ for the expectation with respect to a standard normal variable $Z$, $\Delta t^N=T/N$ and $t^N_n=n\Delta t^N$.
--
--   Then there is a very good extension of the filtered probability space carrying a Brownian motion $W'$ with
--   $$[W,W']_t=\int_0^t\frac{\tilde E[ZF(s,\sigma_sZ)]}{\sqrt{\tilde E[F^2(s,\sigma_sZ)]}}\,ds,$$
--   such that the discrete processes
--   $$\sqrt{\Delta t^N}\sum_{n=1}^{\lceil t/\Delta t^N\rceil}F\Big(t^N_{n-1},\tfrac{1}{\sqrt{\Delta t^N}}\Delta X^N_n\Big)$$
--   converge stably in law on $[0,T]$ to
--   $$\int_0^t\Big(b_s\tilde E[\partial_xF(s,\sigma_sZ)]+\frac{\tilde\sigma_s}{2}\tilde E\big[(Z^2-1)\partial_xF(s,\sigma_sZ)\big]\Big)ds+\int_0^t\sqrt{\tilde E[F^2(s,\sigma_sZ)]}\,dW'_s.$$
--
--   This is the compact form, in the absence of jumps, of the functional central limit theorem of Jacod and Protter (2012, Theorem 10.3.2(a)) that the paper uses to prove Theorem 3.3.
--
--   **Formalization Note** The paper writes $\lceil Nt\rceil$, which is the number of grid steps up to $t$ only for $T=1$; the statement uses $\lceil t/\Delta t^N\rceil$, capped at $N$. Stable convergence in law is tested against bounded measurable $Y$ on $\Omega$ times bounded path functionals that are Lipschitz for the uniform distance on $[0,T]$; the limit has continuous paths, for which this is equivalent to stable convergence in the Skorohod topology. The conclusion is existential in the extension and in $W'$, and includes that $\int\sqrt{\tilde E[F^2]}\,dW'$ is a continuous Itô integral. The coefficients are set to $0$ after $T$. The footnote stating that $W'$ and $W^\perp$ have zero covariation is not part of the statement.
-- source:
--   Muhle-Karbe, Wang & Webster, Stochastic liquidity as a proxy for nonlinear price impact, SSRN 4286108 (version of November 2, 2023), p. 25, Theorem A.3 (under Assumption A.1, p. 24, and Assumption A.2, p. 25)

import Mathlib
import Definitions.Def_PropagatorLimit_Scaling_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace PropagatorLimit.Scaling

/-- Theorem A.3, p. 25: under Assumptions A.1 and A.2, the normalized sums
`√Δt^N Σ_{n ≤ ⌈t/Δt^N⌉} F(t^N_{n−1}, ΔX^N_n / √Δt^N)` converge stably in law on `[0, T]` to
`∫₀ᵗ (b_s Ẽ[∂ₓF(s, σ_s Z)] + (σ̃_s/2) Ẽ[(Z² − 1) ∂ₓF(s, σ_s Z)]) ds + ∫₀ᵗ √(Ẽ[F²(s, σ_s Z)]) dW′_s`,
for a Brownian motion `W′` on a very good extension with
`[W, W′]_t = ∫₀ᵗ Ẽ[Z F(s, σ_s Z)] / √(Ẽ[F²(s, σ_s Z)]) ds`. -/
theorem theorem_A_3 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (W Wperp : ℝ≥0 → Ω → ℝ)
    (hW : IsBrownianPair P 𝓕 W Wperp) (S : ItoSV Ω) (hS : IsItoSV P 𝓕 W Wperp S)
    (T : ℝ≥0) (hT : 0 < T) (F : ℝ≥0 → ℝ → ℝ) (G : ℝ → ℝ) (γ : ℝ) (hF : IsA2 T F G γ) :
    ∃ (E : Extension Ω P 𝓕) (Wp J : ℝ≥0 → E.Ω' → ℝ),
      E.IsVeryGood ∧ IsFBrownian E.P' E.𝓖 Wp ∧
      EthierKurtz.HasCrossVariation E.P' (fun t ω' => W t (E.π ω')) Wp
        (fun t ω' => ∫ u in (0 : ℝ)..t.val, corrA3 T F u.toNNReal (S.σ u.toNNReal (E.π ω'))) ∧
      EthierKurtz.HasBrownianItoIntegral E.P' (fun t => E.𝓖 t) Wp
        (fun s ω' => volA3 T F s (S.σ s (E.π ω'))) J ∧
      (∀ ω', Continuous (J · ω')) ∧
      StablyConverges P T (fun N ω t => stepSum T N F S.X ω t) E
        (fun ω' t => (∫ u in (0 : ℝ)..t.val,
            driftA3 F u.toNNReal (S.b u.toNNReal (E.π ω')) (S.σ u.toNNReal (E.π ω'))
              (S.σt u.toNNReal (E.π ω'))) + J t ω') := by sorry

end PropagatorLimit.Scaling
