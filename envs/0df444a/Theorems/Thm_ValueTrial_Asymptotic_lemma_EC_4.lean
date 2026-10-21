-- Prove2me | Theorems.Thm_ValueTrial_Asymptotic_lemma_EC_4
-- name    : ValueTrial.Asymptotic.lemma_EC_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:23.338567+00:00
-- url     : https://prove2.me/theorems/ddd9ab9f-875f-41f3-baed-00cfb26e459d
-- title:
--   Lemma EC.4, p. ec14 (PDF 51) — Case IV: V*/(ζ(H−∆)) converges; r* and KT* grow like (ζ(H−∆))^{1/4}
-- statement:
--   Consider the value-based trial model under its standing assumptions, without discounting, with the affine setup cost $c_{cap}(r)=c_{fix}+c_rr$, $c_{fix}\ge0$, $c_r>0$, the fixed horizon $P(T)=\zeta(H-T-\mathbf 1_{T>0}\Delta)$, durations $T\in[0,H-\Delta]$ and rates $r\ge0$ (no bounds $T_{\max}$, $r_{\max}$). Write $C=c-\delta_{on}(1-2p_N)\mu_0/2$ and
--   $$
--   K=\frac{\sigma_X\zeta\big(\Psi(\mu_0/\sigma_0)+(1-p_N)\mu_0/\sigma_0\big)}{\sqrt{n_0}\,c_r}.
--   $$
--   1. If $C\ge0$, then for all sufficiently large $H$ an optimal design exists, and for every choice of optimal designs
--   $$
--   \lim_{H\to\infty}\frac{V^*}{\zeta(H-\Delta)}=(1-p_N)\sigma_0\Psi(-\mu_0/\sigma_0)+p_N\sigma_0\Psi(\mu_0/\sigma_0).
--   $$
--   2. If $C>0$, then for every choice of optimal designs
--   $$
--   \lim_{H\to\infty}\frac{r^*}{(\zeta(H-\Delta))^{1/4}}=\lim_{H\to\infty}\frac{KT^*}{(\zeta(H-\Delta))^{1/4}}=\left(\frac{K^2\sqrt{n_0\sigma_X^2}\,\phi(\mu_0/\sigma_0)}{c-\delta_{on}(1-2p_N)\mu_0/2}\right)^{1/4}.
--   $$
--
--   The product of the two rates gives Case IV of Proposition 5; both decision variables grow without bound, at the same rate $H^{1/4}$.
--
--   **Formalization Note** Durations are capped at $H-\Delta$ (the fixed-horizon population is negative beyond it; §2.4.1, Table EC.1). The lemma's further branch $C=0$ (rates $(\zeta(H-\Delta))^{1/3}$) is not part of this statement. The printed lemma labels the $C>0$ display "if $c-\delta_{on}(1-2p_N)\mu_0/2=0$"; the sentence before it says $>0$, which is what is stated. Limits are asserted for every selection of optimizers, with existence for large $H$ as an extra conjunct in part 1 (which covers part 2).
-- source:
--   Alban, Chick & Forster, Value-based clinical trials, accepted manuscript (Management Science 69(6), 2023; IRIS UniBo 11585/879132), p. ec14 (PDF 51), App. C.4.4, Lemma EC.4 (first display and the c − δon(1 − 2pN)µ0/2 > 0 branch)

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter

namespace ValueTrial.Asymptotic

/-- Lemma EC.4, p. ec14 (PDF 51) — Case IV with `Tmax = ∞` and `rmax = ∞`: with no discounting,
the affine setup cost `ccap(r) = cfix + cr r`, `cr > 0`, and the fixed horizon
`P(T) = ζ(H - T - 1_{T>0}∆)` (trial lengths `T ∈ [0, H - ∆]`):
(a) if `c - δon(1 - 2pN)µ0/2 ≥ 0`, optimal designs exist for all large `H` and every selection of
them has `V*/(ζ(H - ∆)) → (1 - pN)σ0Ψ(-µ0/σ0) + pNσ0Ψ(µ0/σ0)`;
(b) if `c - δon(1 - 2pN)µ0/2 > 0`, every selection of optimal designs has
`r*/(ζ(H - ∆))^{1/4} → L` and `K T*/(ζ(H - ∆))^{1/4} → L`, where
`L = (K² √(n0σX²) ϕ(µ0/σ0) / (c - δon(1 - 2pN)µ0/2))^{1/4}` and
`K = σX ζ (Ψ(µ0/σ0) + (1 - pN)µ0/σ0) / (√n0 cr)`. -/
theorem lemma_EC_4 (θ : Params) (hS : θ.Standing) (hρ : θ.rho = 0) (cfix cr : ℝ)
    (hcfix : 0 ≤ cfix) (hcr : 0 < cr) :
    let K : ℝ := θ.sigX * θ.zeta *
      (InventoryControl.normalLoss (θ.mu0 / sig0 θ) + (1 - θ.pN) * θ.mu0 / sig0 θ) /
        (Real.sqrt θ.n0 * cr)
    (0 ≤ Cnet θ →
      (∀ᶠ H in atTop, ∃ x : ℝ × ℝ,
          IsOptOn (V θ (fun r => cfix + cr * r) (fixedHorizon θ H))
            {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ 0 ≤ x.2} x) ∧
      ∀ xs : ℝ → ℝ × ℝ,
        (∀ᶠ H in atTop, IsOptOn (V θ (fun r => cfix + cr * r) (fixedHorizon θ H))
            {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ 0 ≤ x.2} (xs H)) →
        Tendsto (fun H => V θ (fun r => cfix + cr * r) (fixedHorizon θ H) (xs H) /
            (θ.zeta * (H - θ.Del))) atTop (nhds (vInf θ))) ∧
    (0 < Cnet θ →
      ∀ xs : ℝ → ℝ × ℝ,
        (∀ᶠ H in atTop, IsOptOn (V θ (fun r => cfix + cr * r) (fixedHorizon θ H))
            {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ 0 ≤ x.2} (xs H)) →
        Tendsto (fun H => (xs H).2 / (θ.zeta * (H - θ.Del)) ^ ((1 : ℝ) / 4)) atTop
            (nhds ((K ^ 2 * Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ / Cnet θ) ^ ((1 : ℝ) / 4))) ∧
          Tendsto (fun H => K * (xs H).1 / (θ.zeta * (H - θ.Del)) ^ ((1 : ℝ) / 4)) atTop
            (nhds ((K ^ 2 * Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ / Cnet θ) ^ ((1 : ℝ) / 4)))) := by sorry

end ValueTrial.Asymptotic
