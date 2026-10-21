-- Prove2me | Theorems.Thm_ValueTrial_Asymptotic_proposition_5
-- name    : ValueTrial.Asymptotic.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:35.081105+00:00
-- url     : https://prove2.me/theorems/c7ceb561-375b-4ee6-bbb4-692da3740750
-- title:
--   Proposition 5, pp. 18–19 (PDF 20–21) — the optimal sample size grows as the square root of the post-adoption population (Case III constant corrected)
-- statement:
--   Consider the value-based trial model under its standing assumptions, without discounting ($\rho=0$), with setup cost $c_{cap}(r)=c_{fix}+c_rr$, $c_{fix}\ge0$, $c_r\ge0$, and
--   $$
--   C=c-\delta_{on}(1-2p_N)\mu_0/2>0 .
--   $$
--   Write $\phi$ for the standard normal density, $\Psi$ for the standard normal linear loss, $\sigma_0=\sigma_X/\sqrt{n_0}$, and
--   $$
--   v_\infty=(1-p_N)\sigma_0\Psi(-\mu_0/\sigma_0)+p_N\sigma_0\Psi(\mu_0/\sigma_0).
--   $$
--   The decision sets are those of §3.6.1: in Cases I and II the rate is fixed at $0<r=r_{\max}\le\zeta$ and $T\ge0$ is free; in Case III the duration is fixed at $T=T_{\max}>0$ and $r\ge0$ is free; in Case IV both are free; under the fixed horizon $P(T)=\zeta(H-T-\mathbf 1_{T>0}\Delta)$ the trial ends by $H-\Delta$. In each case, optimal designs exist for all sufficiently large $P$ (resp. $H$), and every choice of optimal designs, with $Q^*=T^*r^*/2$, satisfies:
--
--   1. **Case I** ($c_r=0$, fixed patient pool $P$): $\displaystyle\lim_{P\to\infty}\frac{Q^*}{\sqrt P}=\left(\frac{\sqrt{n_0\sigma_X^2}\,\phi(\mu_0/\sigma_0)}{4C}\right)^{1/2}$ and $\displaystyle\lim_{P\to\infty}\frac{V^*}{P}=v_\infty$.
--   2. **Case III** ($c_r>0$, fixed patient pool $P$): $\displaystyle\lim_{P\to\infty}\frac{Q^*}{\sqrt P}=\left(\frac{\sqrt{n_0\sigma_X^2}\,\phi(\mu_0/\sigma_0)}{4(C+c_r/T_{\max})}\right)^{1/2}$ and $\displaystyle\lim_{P\to\infty}\frac{V^*}{P}=v_\infty$.
--   3. **Case II** ($c_r=0$, fixed horizon): $\displaystyle\lim_{H\to\infty}\frac{V^*}{\zeta(H-\Delta)}=v_\infty$ and
--   $$
--   \lim_{H\to\infty}\frac{Q^*}{\sqrt{\zeta(H-\Delta)}}=\left(\frac{\sqrt{n_0\sigma_X^2}\,\phi(\mu_0/\sigma_0)}{4C+4\zeta\sigma_0\big(\Psi(\mu_0/\sigma_0)+(1-p_N)\mu_0/\sigma_0\big)/r_{\max}}\right)^{1/2}.
--   $$
--   4. **Case IV** ($c_r>0$, fixed horizon): $\displaystyle\lim_{H\to\infty}\frac{V^*}{\zeta(H-\Delta)}=v_\infty$ and $\displaystyle\lim_{H\to\infty}\frac{Q^*}{\sqrt{\zeta(H-\Delta)}}=\left(\frac{\sqrt{n_0\sigma_X^2}\,\phi(\mu_0/\sigma_0)}{4C}\right)^{1/2}$.
--
--   The optimal sample size grows like the square root of the post-adoption population, the optimal value per post-adoption patient tends to the same $v_\infty$ under a fixed pool and a fixed horizon, and the switching costs $I_N,I_S$ drop out of every limit.
--
--   **Formalization Note** (i) The page prints the Case I constant for Case III as well; with $T=T_{\max}$ fixed the cost of $Q$ pairs is $c_{fix}+2Q(C+c_r/T_{\max})$, so $C$ must be replaced by $C+c_r/T_{\max}$ (numerically, at $p_N=0.3,\mu_0=0.4,n_0=2,\sigma_X=3,c=1,\delta_{on}=1,c_r=2,T_{\max}=3$: $Q^*/\sqrt P=0.5118$ at $P=10^{10}$ against the corrected $0.5118$ and the printed $0.6722$). The statement uses the corrected constant. (ii) "$Q^*$" presupposes an optimal design; the limits hold for every selection of optimizers, and existence for large $P$ (resp. $H$) is asserted as an extra conjunct so that the statement is not vacuous. (iii) The cap $T\le H-\Delta$ under the fixed horizon keeps $P(T)\ge0$ (§2.4.1, Table EC.1). (iv) $c_{fix}\ge0$ is the model's nonnegative setup cost.
-- source:
--   Alban, Chick & Forster, Value-based clinical trials, accepted manuscript (Management Science 69(6), 2023; IRIS UniBo 11585/879132), pp. 18–19 (PDF 20–21), §3.6.1, Proposition 5 (Case III constant corrected); proof App. C.4, pp. ec10–ec16 (PDF 47–53)

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter

namespace ValueTrial.Asymptotic

/-- Proposition 5, pp. 18–19 (PDF 20–21), Case III constant corrected. Assume
`c - δon(1 - 2pN)µ0/2 > 0`, `ρ = 0` and `ccap(r) = cfix + cr r` with `cr ≥ 0`, and use the decision sets of
§3.6.1 (Cases I and II: `r = rmax` with `0 < rmax ≤ ζ`, `T` free; Case III: `T = Tmax`, `r` free; Case IV: both free; with
a fixed horizon the trial ends by `H - ∆`). In each case optimal designs exist for all large `P`
(resp. `H`), and every selection of optimal designs, with `Q* = T* r*/2`, satisfies:
* Case I (`cr = 0`, fixed pool): `Q*/√P → (√(n0σX²) ϕ(µ0/σ0) / (4C))^{1/2}`, `V*/P → v∞`;
* Case III (`cr > 0`, fixed pool): `Q*/√P → (√(n0σX²) ϕ(µ0/σ0) / (4(C + cr/Tmax)))^{1/2}`
  (the page prints the Case I constant), `V*/P → v∞`;
* Case II (`cr = 0`, fixed horizon): `V*/(ζ(H - ∆)) → v∞` and
  `Q*/√(ζ(H - ∆)) → (√(n0σX²) ϕ(µ0/σ0) / (4C + 4ζσ0(Ψ(µ0/σ0) + (1 - pN)µ0/σ0)/rmax))^{1/2}`;
* Case IV (`cr > 0`, fixed horizon): `V*/(ζ(H - ∆)) → v∞` and
  `Q*/√(ζ(H - ∆)) → (√(n0σX²) ϕ(µ0/σ0) / (4C))^{1/2}`;
where `C = c - δon(1 - 2pN)µ0/2` and `v∞ = (1 - pN)σ0Ψ(-µ0/σ0) + pNσ0Ψ(µ0/σ0)`. -/
theorem proposition_5 (θ : Params) (hS : θ.Standing) (hρ : θ.rho = 0) (cfix cr : ℝ)
    (hcfix : 0 ≤ cfix) (hcr : 0 ≤ cr) (hC : 0 < Cnet θ) :
    -- Case I: cr = 0, fixed patient pool, r = rmax
    (cr = 0 → ∀ rmax : ℝ, 0 < rmax → rmax ≤ θ.zeta →
      (∀ᶠ P in atTop, ∃ x : ℝ × ℝ,
          IsOptOn (V θ (fun r => cfix + cr * r) (fixedPool P)) {x | 0 ≤ x.1 ∧ x.2 = rmax} x) ∧
      ∀ xs : ℝ → ℝ × ℝ,
        (∀ᶠ P in atTop, IsOptOn (V θ (fun r => cfix + cr * r) (fixedPool P))
            {x | 0 ≤ x.1 ∧ x.2 = rmax} (xs P)) →
        Tendsto (fun P => (xs P).1 * (xs P).2 / 2 / Real.sqrt P) atTop
            (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ / (4 * Cnet θ)))) ∧
          Tendsto (fun P => V θ (fun r => cfix + cr * r) (fixedPool P) (xs P) / P) atTop
            (nhds (vInf θ))) ∧
    -- Case III (constant corrected): cr > 0, fixed patient pool, T = Tmax
    (0 < cr → ∀ Tmax : ℝ, 0 < Tmax →
      (∀ᶠ P in atTop, ∃ x : ℝ × ℝ,
          IsOptOn (V θ (fun r => cfix + cr * r) (fixedPool P)) {x | x.1 = Tmax ∧ 0 ≤ x.2} x) ∧
      ∀ xs : ℝ → ℝ × ℝ,
        (∀ᶠ P in atTop, IsOptOn (V θ (fun r => cfix + cr * r) (fixedPool P))
            {x | x.1 = Tmax ∧ 0 ≤ x.2} (xs P)) →
        Tendsto (fun P => (xs P).1 * (xs P).2 / 2 / Real.sqrt P) atTop
            (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ /
              (4 * (Cnet θ + cr / Tmax))))) ∧
          Tendsto (fun P => V θ (fun r => cfix + cr * r) (fixedPool P) (xs P) / P) atTop
            (nhds (vInf θ))) ∧
    -- Case II: cr = 0, fixed horizon, r = rmax
    (cr = 0 → ∀ rmax : ℝ, 0 < rmax → rmax ≤ θ.zeta →
      (∀ᶠ H in atTop, ∃ x : ℝ × ℝ,
          IsOptOn (V θ (fun r => cfix + cr * r) (fixedHorizon θ H))
            {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ x.2 = rmax} x) ∧
      ∀ xs : ℝ → ℝ × ℝ,
        (∀ᶠ H in atTop, IsOptOn (V θ (fun r => cfix + cr * r) (fixedHorizon θ H))
            {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ x.2 = rmax} (xs H)) →
        Tendsto (fun H => V θ (fun r => cfix + cr * r) (fixedHorizon θ H) (xs H) /
            (θ.zeta * (H - θ.Del))) atTop (nhds (vInf θ)) ∧
          Tendsto (fun H => (xs H).1 * (xs H).2 / 2 / Real.sqrt (θ.zeta * (H - θ.Del))) atTop
            (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ /
              (4 * Cnet θ + 4 * θ.zeta * sig0 θ *
                (InventoryControl.normalLoss (θ.mu0 / sig0 θ)
                  + (1 - θ.pN) * θ.mu0 / sig0 θ) / rmax))))) ∧
    -- Case IV: cr > 0, fixed horizon, T and r free
    (0 < cr →
      (∀ᶠ H in atTop, ∃ x : ℝ × ℝ,
          IsOptOn (V θ (fun r => cfix + cr * r) (fixedHorizon θ H))
            {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ 0 ≤ x.2} x) ∧
      ∀ xs : ℝ → ℝ × ℝ,
        (∀ᶠ H in atTop, IsOptOn (V θ (fun r => cfix + cr * r) (fixedHorizon θ H))
            {x | 0 ≤ x.1 ∧ x.1 ≤ H - θ.Del ∧ 0 ≤ x.2} (xs H)) →
        Tendsto (fun H => V θ (fun r => cfix + cr * r) (fixedHorizon θ H) (xs H) /
            (θ.zeta * (H - θ.Del))) atTop (nhds (vInf θ)) ∧
          Tendsto (fun H => (xs H).1 * (xs H).2 / 2 / Real.sqrt (θ.zeta * (H - θ.Del))) atTop
            (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ / (4 * Cnet θ))))) := by sorry

end ValueTrial.Asymptotic
