-- Prove2me | Theorems.Thm_ValueTrial_Asymptotic_lemma_EC_1
-- name    : ValueTrial.Asymptotic.lemma_EC_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:17:17.240998+00:00
-- url     : https://prove2.me/theorems/416e30fa-d108-4ca0-a0f8-1e9d45cb2f8e
-- title:
--   Lemma EC.1, p. ec10 (PDF 47) — Case I: Q*/√P and V*/P converge
-- statement:
--   Consider the value-based trial model under its standing assumptions, without discounting, with a constant setup cost $k\ge0$, a fixed patient pool $P$, unbounded decisions ($T_{\max}=r_{\max}=\infty$, i.e. $T,r\ge0$), and
--   $$
--   C=c-\delta_{on}(1-2p_N)\mu_0/2>0 .
--   $$
--   Then for all sufficiently large $P$ an optimal design exists, and for every choice $(T^*(P),r^*(P))$ of optimal designs, with $Q^*=T^*r^*/2$,
--   $$
--   \lim_{P\to\infty}\frac{Q^*}{\sqrt P}=\left(\frac{\sqrt{n_0\sigma_X^2}\,\phi(\mu_0/\sigma_0)}{4\big(c-\delta_{on}(1-2p_N)\mu_0/2\big)}\right)^{1/2},\qquad
--   \lim_{P\to\infty}\frac{V^*}{P}=(1-p_N)\sigma_0\Psi(-\mu_0/\sigma_0)+p_N\sigma_0\Psi(\mu_0/\sigma_0).
--   $$
--   Here $\phi$ is the standard normal density and $\Psi$ the standard normal linear loss.
--
--   This is Case I of Proposition 5.
--
--   **Formalization Note** "$Q^*$" presupposes an optimal design and does not say which; the limits are asserted for every selection of optimizers, and the existence of optimizers for large $P$ is stated as an additional conjunct, so that the statement is not vacuous. The setup cost is required nonnegative (model convention).
-- source:
--   Alban, Chick & Forster, Value-based clinical trials, accepted manuscript (Management Science 69(6), 2023; IRIS UniBo 11585/879132), p. ec10 (PDF 47), App. C.4.1, Lemma EC.1

import Mathlib
import Definitions.Def_ValueTrial_Asymptotic_Model

open MeasureTheory ProbabilityTheory Filter

namespace ValueTrial.Asymptotic

/-- Lemma EC.1, p. ec10 (PDF 47) — Case I with `rmax = ∞` and `Tmax = ∞`: with a constant setup
cost, no discounting, a fixed patient pool `P` and `c - δon(1 - 2pN)µ0/2 > 0`, optimal designs exist
for all large `P`, and for every selection `(T*(P), r*(P))` of optimal designs the sample size
`Q* = T* r*/2` and the optimal value `V*` satisfy
`Q*/√P → (√(n0σX²) ϕ(µ0/σ0) / (4(c - δon(1 - 2pN)µ0/2)))^{1/2}` and
`V*/P → (1 - pN)σ0Ψ(-µ0/σ0) + pNσ0Ψ(µ0/σ0)`. -/
theorem lemma_EC_1 (θ : Params) (hS : θ.Standing) (hρ : θ.rho = 0) (k : ℝ) (hk : 0 ≤ k)
    (hC : 0 < Cnet θ) :
    (∀ᶠ P in atTop, ∃ x : ℝ × ℝ,
        IsOptOn (V θ (fun _ => k) (fixedPool P)) (Set.Ici 0 ×ˢ Set.Ici 0) x) ∧
    ∀ xs : ℝ → ℝ × ℝ,
      (∀ᶠ P in atTop, IsOptOn (V θ (fun _ => k) (fixedPool P)) (Set.Ici 0 ×ˢ Set.Ici 0) (xs P)) →
      Tendsto (fun P => (xs P).1 * (xs P).2 / 2 / Real.sqrt P) atTop
          (nhds (Real.sqrt (Real.sqrt (θ.n0 * θ.sigX ^ 2) * phi0 θ / (4 * Cnet θ)))) ∧
        Tendsto (fun P => V θ (fun _ => k) (fixedPool P) (xs P) / P) atTop (nhds (vInf θ)) := by sorry

end ValueTrial.Asymptotic
