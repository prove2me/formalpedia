-- Prove2me | Theorems.Thm_ValueTrial_Asymptotic_lemma_EC_3
-- name    : ValueTrial.Asymptotic.lemma_EC_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:43.489654+00:00
-- url     : https://prove2.me/theorems/d54115e8-8c49-4aa0-8b2e-0cdfd464f9b7
-- title:
--   Lemma EC.3 (corrected), p. ec13 (PDF 50) — Case III: r*/√P and V*/P converge
-- statement:
--   Consider the value-based trial model under its standing assumptions, without discounting, with the affine setup cost $c_{cap}(r)=c_{fix}+c_rr$, $c_{fix}\ge0$, $c_r>0$, a fixed patient pool $P$, trial duration fixed at $T=T_{\max}>0$, rates $r\ge0$ (no upper bound $r_{\max}$), and $C=c-\delta_{on}(1-2p_N)\mu_0/2>0$. Then for all sufficiently large $P$ an optimal rate exists, and for every choice of optimal designs
--   $$
--   \lim_{P\to\infty}\frac{r^*}{\sqrt P}=\left(\frac{\sqrt{n_0\sigma_X^2}\,\phi(\mu_0/\sigma_0)}{T_{\max}\big[cT_{\max}+c_r-\delta_{on}(1-2p_N)\mu_0T_{\max}/2\big]}\right)^{1/2},\qquad
--   \lim_{P\to\infty}\frac{V^*}{P}=\sigma_0\big[\Psi(\mu_0/\sigma_0)+(1-p_N)\mu_0/\sigma_0\big].
--   $$
--
--   Multiplied by $T_{\max}/2$ this gives Case III of Proposition 5.
--
--   **Formalization Note** The printed (EC.4) has denominator $cT_{\max}+c_r-\delta_{on}(1-2p_N)\mu_0T_{\max}/2$ without the factor $T_{\max}$. The proof's own optimality condition (p. ec13) gives the factor: its right side is asymptotically $r^{*2}T_{\max}(c_r+CT_{\max})/\sqrt{n_0\sigma_X^2}$ and its left side $P\phi(\mu_0/\sigma_0)$. Equivalently, with $T=T_{\max}$ fixed the cost is $c_{fix}+2Q(C+c_r/T_{\max})$, the Case I cost with $C$ replaced by $C+c_r/T_{\max}$. The statement uses the corrected constant; the limit of $V^*/P$ is as printed. Limits are asserted for every selection of optimizers, with existence for large $P$ as an extra conjunct.
-- source:
--   Alban, Chick & Forster, Value-based clinical trials, accepted manuscript (Management Science 69(6), 2023; IRIS UniBo 11585/879132), p. ec13 (PDF 50), App. C.4.3, Lemma EC.3, eq. (EC.4) (corrected)

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter

namespace ValueTrial.Asymptotic

/-- Lemma EC.3 (corrected), p. ec13 (PDF 50) — Case III with `rmax = ∞` and `T = Tmax`
(Proposition 4): with the affine setup cost `ccap(r) = cfix + cr r`, `cr > 0`, no discounting, a fixed
patient pool `P` and `c - δon(1 - 2pN)µ0/2 > 0`, optimal designs exist for all large `P`, and for
every selection of optimal designs
`r*/√P → (√(n0σX²) ϕ(µ0/σ0) / (Tmax [c Tmax + cr - δon(1 - 2pN)µ0 Tmax/2]))^{1/2}` and
`V*/P → σ0[Ψ(µ0/σ0) + (1 - pN)µ0/σ0]`.
The printed (EC.4) lacks the factor `Tmax` in the denominator; the proof's optimality condition on
p. ec13 gives it. -/
theorem lemma_EC_3 (θ : Params) (hS : θ.Standing) (hρ : θ.rho = 0) (cfix cr : ℝ)
    (hcfix : 0 ≤ cfix) (hcr : 0 < cr) (Tmax : ℝ) (hTmax : 0 < Tmax) (hC : 0 < Cnet θ) :
    (∀ᶠ P in atTop, ∃ x : ℝ × ℝ,
        IsOptOn (V θ (fun r => cfix + cr * r) (fixedPool P)) {x | x.1 = Tmax ∧ 0 ≤ x.2} x) ∧
    ∀ xs : ℝ → ℝ × ℝ,
      (∀ᶠ P in atTop, IsOptOn (V θ (fun r => cfix + cr * r) (fixedPool P))
          {x | x.1 = Tmax ∧ 0 ≤ x.2} (xs P)) →
      Tendsto (fun P => (xs P).2 / Real.sqrt P) atTop
          (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ /
            (Tmax * (θ.c * Tmax + cr - θ.don * (1 - 2 * θ.pN) * θ.mu0 * Tmax / 2))))) ∧
        Tendsto (fun P => V θ (fun r => cfix + cr * r) (fixedPool P) (xs P) / P) atTop
          (nhds (sig0 θ * (InventoryControl.normalLoss (θ.mu0 / sig0 θ)
            + (1 - θ.pN) * θ.mu0 / sig0 θ))) := by sorry

end ValueTrial.Asymptotic
