-- Prove2me | Theorems.Thm_SWSSNet_Diffusion_remark_8
-- name    : SWSSNet.Diffusion.remark_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:26.914984+00:00
-- url     : https://prove2.me/theorems/f9647f74-5fd6-48ab-a563-faa28750e24d
-- title:
--   Remark 8 — ζ = B₁⁻¹h + ϑ_pB₁⁻¹p has ⟨e,ζ⟩ = 0, and X̆ = X̃ + ζ
-- statement:
--   Let $B_1$ be the matrix of (38) for a pool $\hat\jmath$, $h$ the vector (12), $p$ a positive probability vector, and
--   $$
--   \zeta=B_1^{-1}h+\vartheta_pB_1^{-1}p .
--   $$
--   Then:
--
--   1. $\langle e,\zeta\rangle=0$.
--   2. For every control value $u$ and state $x$, the drift with $h$ at $x+\zeta$ equals the recentred drift $\tilde b$ (the same drift with $-\vartheta_pp$ in place of $h$) at $x$:
--   $$
--   \breve b(x+\zeta,u)=\tilde b(x,u).
--   $$
--   3. For every stationary Markov control $v$, if $\tilde X$ is a strong solution of $d\tilde X_t=\tilde b(\tilde X_t,v(\tilde X_t))dt+\Sigma dW_t$ from $x$, then $\breve X=\tilde X+\zeta$ is a strong solution, driven by the same Brownian motion, of $d\breve X_t=\breve b(\breve X_t,U_t)dt+\Sigma dW_t$ from $x+\zeta$. Here $U_t=v(\breve X_t-\zeta)$.
--
--   The two centrings of the diffusion therefore differ by a constant shift, and their ergodic properties coincide. This transfers the stability result of Theorem 7, proved for $\tilde b$, to the drift of (12).
-- source:
--   Hmedi, Arapostathis & Pang, On System-Wide Safety Staffing of Large-Scale Parallel Server Networks, arXiv:2009.01942v3, pp. 27–28, Remark 8

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_UnifErgHW_Diffusion_Lyapunov
import Definitions.Def_SWSSNet_Diffusion_Network
import Definitions.Def_SWSSNet_Diffusion_Process

open Matrix MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace SWSSNet.Diffusion

/-- Remark 8, p. 28: for the matrix `B₁` of any pool `ĵ`, `ζ = B₁⁻¹h + ϑ_p B₁⁻¹p` satisfies
`⟨e,ζ⟩ = 0`; the drift with `h` of (12) at `x + ζ` equals the recentred drift (with `−ϑ_p p` in
place of `h`) at `x`; hence, under the same Brownian motion, a strong solution `X̃` of the recentred
equation gives the strong solution `X̆ = X̃ + ζ` of the original one. -/
theorem remark_8 {I J : ℕ} (N : TreeNetwork I J) (ĵ : Fin J) (p : Fin I → ℝ) (hp : IsPosProb p) :
    let ζ : EthierKurtz.SDEState I := WithLp.toLp 2 ((B1 N ĵ)⁻¹ *ᵥ (hvec N + swss N p • p))
    (∑ i, ζ i = 0) ∧
    (∀ (u : (Fin I → ℝ) × (Fin J → ℝ)) (x : EthierKurtz.SDEState I), IsControlValue u →
      driftH N (hvec N) u (x + ζ) = driftH N (-(swss N p) • p) u x) ∧
    ∀ (v : EthierKurtz.SDEState I → (Fin I → ℝ) × (Fin J → ℝ)), IsMarkovControl v →
      ∀ (Ω : Type) [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
        (B X : ℝ≥0 → Ω → EthierKurtz.SDEState I) (x : EthierKurtz.SDEState I),
        EthierKurtz.IsStandardBrownian Pr B →
        UnifErgHW.Diffusion.IsStrongSolution Pr (markovDrift N (-(swss N p) • p) v) (Sigma N) B X x →
        UnifErgHW.Diffusion.IsStrongSolution Pr (markovDrift N (hvec N) (fun y => v (y - ζ)))
          (Sigma N) B (fun t ω => X t ω + ζ) (x + ζ) := by sorry

end SWSSNet.Diffusion
