-- Prove2me | Theorems.Thm_ValueTrial_Asymptotic_lemma_EC_2
-- name    : ValueTrial.Asymptotic.lemma_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:30.556373+00:00
-- url     : https://prove2.me/theorems/9cebdb23-0af2-4f13-b3ba-74cd10bb66e2
-- title:
--   Lemma EC.2, p. ec12 (PDF 49) — Case II: T*/√(ζ(H−∆)) and V*/(ζ(H−∆)) converge
-- statement:
--   Consider the value-based trial model under its standing assumptions, without discounting, with a constant setup cost $k\ge0$, the fixed horizon $P(T)=\zeta(H-T-\mathbf 1_{T>0}\Delta)$, recruitment at a fixed rate $0<r=r_{\max}\le\zeta$, durations $T\in[0,H-\Delta]$ (no upper bound $T_{\max}$), and $C=c-\delta_{on}(1-2p_N)\mu_0/2>0$. Then for all sufficiently large $H$ an optimal duration exists, and for every choice of optimal designs
--   $$
--   \lim_{H\to\infty}\frac{T^*}{\sqrt{\zeta(H-\Delta)}}=\left(\frac{\sqrt{n_0\sigma_X^2}\,\phi(\mu_0/\sigma_0)}{\big(c-\delta_{on}(1-2p_N)\mu_0/2\big)r_{\max}^2+\zeta r_{\max}\sigma_0\big(\Psi(\mu_0/\sigma_0)+(1-p_N)\mu_0/\sigma_0\big)}\right)^{1/2}, \tag{EC.3}
--   $$
--   $$
--   \lim_{H\to\infty}\frac{V^*}{\zeta(H-\Delta)}=(1-p_N)\sigma_0\Psi(-\mu_0/\sigma_0)+p_N\sigma_0\Psi(\mu_0/\sigma_0).
--   $$
--
--   Multiplied by $r_{\max}/2$ this gives Case II of Proposition 5.
--
--   **Formalization Note** The rate is fixed at $r_{\max}$, as the proof does on the strength of Proposition 3. Durations are capped at $H-\Delta$: beyond it the fixed-horizon population $P(T)$ is negative, outside the model (§2.4.1 requires $H\ge T_{\max}+\Delta$, Table EC.1 $P(T)\ge0$). The limits are asserted for every selection of optimizers, with existence for large $H$ as an extra conjunct.
-- source:
--   Alban, Chick & Forster, Value-based clinical trials, accepted manuscript (Management Science 69(6), 2023; IRIS UniBo 11585/879132), p. ec12 (PDF 49), App. C.4.2, Lemma EC.2, eq. (EC.3)

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter

namespace ValueTrial.Asymptotic

/-- Lemma EC.2, p. ec12 (PDF 49) — Case II with `Tmax = ∞` and `r = rmax` (Proposition 3): with a
constant setup cost, no discounting, the fixed horizon `P(T) = ζ(H - T - 1_{T>0}∆)` (trial lengths
`T ∈ [0, H - ∆]`), `0 < rmax ≤ ζ` and `c - δon(1 - 2pN)µ0/2 > 0`, optimal designs exist for all
large `H`, and every selection of optimal designs has
`T*/√(ζ(H - ∆)) → (√(n0σX²) ϕ(µ0/σ0) / ((c - δon(1 - 2pN)µ0/2) rmax² + ζ rmax σ0 (Ψ(µ0/σ0) + (1 - pN)µ0/σ0)))^{1/2}`
(EC.3) and `V*/(ζ(H - ∆)) → (1 - pN)σ0Ψ(-µ0/σ0) + pNσ0Ψ(µ0/σ0)`. -/
theorem lemma_EC_2 (θ : Params) (hS : θ.Standing) (hρ : θ.rho = 0) (k : ℝ) (hk : 0 ≤ k)
    (rmax : ℝ) (hrmax : 0 < rmax) (hrcap : rmax ≤ θ.zeta) (hC : 0 < Cnet θ) :
    (∀ᶠ H in atTop, ∃ x : ℝ × ℝ,
        IsOptOn (V θ (fun _ => k) (fixedHorizon θ H))
          {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ x.2 = rmax} x) ∧
    ∀ xs : ℝ → ℝ × ℝ,
      (∀ᶠ H in atTop, IsOptOn (V θ (fun _ => k) (fixedHorizon θ H))
          {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ x.2 = rmax} (xs H)) →
      Tendsto (fun H => (xs H).1 / Real.sqrt (θ.zeta * (H - θ.Del))) atTop
          (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ /
            (Cnet θ * rmax ^ 2 + θ.zeta * rmax * sig0 θ *
              (InventoryControl.normalLoss (θ.mu0 / sig0 θ)
                + (1 - θ.pN) * θ.mu0 / sig0 θ))))) ∧
        Tendsto (fun H => V θ (fun _ => k) (fixedHorizon θ H) (xs H) / (θ.zeta * (H - θ.Del)))
          atTop (nhds (vInf θ)) := by sorry

end ValueTrial.Asymptotic
