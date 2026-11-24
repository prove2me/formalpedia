-- Prove2me | Theorems.Thm_SocialManip_Beliefs_Supplement_theorem_3
-- name    : SocialManip.Beliefs.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:15:51.799798+00:00
-- url     : https://prove2.me/theorems/e890a624-c1a5-4278-ab2c-dbf46b0a4d25
-- title:
--   Theorem 3, pp. 16–17 — cutoffs 0 < θ̲ < θ* < θ̄ < 1: homogeneous preservations are impervious for small θ′, and for b > 1/2 susceptible on (θ*, θ̄)
-- statement:
--   Fix a homogeneous network $G_\theta$: every DeGroot agent has experience weight $\theta\in(0,1)$, the standing constraints and Assumption 1 hold, $q\in(0,1)$, $\lambda,\lambda^*>0$, $b\in(-1,1)$, there is at least one Bayesian agent, and at least one DeGroot agent has no link to a Bayesian. For $\theta'\in(0,1)$ let $G_{\theta'}$ be the homogeneous network preservation: experience weights $\theta'$ and DeGroot weights $w'_{ij}=w_{ij}(1-\theta')/(1-\theta)$. Then there exist cutoffs
--   $$0<\underline\theta<\theta^*<\overline\theta<1$$
--   such that:
--   1. (a) if $\theta'\in(0,\underline\theta)$, the network $G_{\theta'}$ is impervious for every $\varepsilon>0$;
--   2. (b) for every $\varepsilon>0$: if $G_{\theta'}$ is impervious for every $\theta'\in(\theta^*,\overline\theta)$, then it is impervious for every $\theta'\in(\theta^*,1)$;
--   3. (c) if $b>1/2$, there is $\varepsilon>0$ such that $G_{\theta'}$ is susceptible for every $\theta'\in(\theta^*,\overline\theta)$ and impervious for every $\theta'\in(\overline\theta,1)$.
--
--   Manipulation is non-monotone in the weight a society places on personal experience: herding societies (small $\theta'$) and individualistic ones (large $\theta'$) resist it, intermediate ones may not.
--
--   **Formalization Note** Imperviousness and susceptibility are those of the definition item *Game*. The cutoffs depend on the fixed network and on $b$, not on $\varepsilon$.
--
--   Differences from the source:
--   - reading: clause (c) prints θ ∈ (θ̄, 1) for G_θ′ → θ′ ∈ (θ̄, 1); reason: θ′ is the varying parameter; the proof (pp. 48–49) treats θ′ ∈ (θ̄, 1)
--   - reading: a DeGroot not adjacent to a Bayesian → a DeGroot with zero weight on every Bayesian; reason: the proof uses only this agent's own links
--   - reading: (b) for any ε > 0 → the implication for each fixed ε; reason: the proof argues for each ε
--   - reading: arbitrary self-experience weight θ → θ ∈ (0,1); reason: Definition 5 divides by 1 − θ; Assumption 1(iii) for G_θ′ forces θ > 0
--   - reading: impervious = no agent manipulated in equilibrium → asymptotically in T, probability → 1 in every equilibrium; reason: the paper evaluates manipulation as T → ∞
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), Theorem 3, pp. 16–17; Definition 5 and the homogeneous setting p. 16; proof pp. 48–49

import Mathlib
import Definitions.Def_SocialManip_Beliefs_Setting
import Definitions.Def_SocialManip_Beliefs_Supplement_Network
import Definitions.Def_SocialManip_Beliefs_Supplement_Game

namespace SocialManip.Beliefs.Supplement

open SocialManip.Beliefs

theorem theorem_3 {n : ℕ} (M : Model n) (hS : M.Standing) (hq : 0 < M.q ∧ M.q < 1)
    (hlam : 0 < M.lam) (hlamStar : 0 < M.lamStar) (hb : -1 < M.b ∧ M.b < 1)
    (adj : Fin n → Fin n → Prop) (hA : M.Assumption1 adj)
    (θ₀ : ℝ) (hθ₀ : 0 < θ₀ ∧ θ₀ < 1) (hhom : ∀ i ∉ M.B, M.θ i = θ₀)
    (hBayes : M.B.Nonempty) (hfar : ∃ i ∉ M.B, ∀ j ∈ M.B, M.α i j = 0) :
    ∃ θlow θstar θup : ℝ, 0 < θlow ∧ θlow < θstar ∧ θstar < θup ∧ θup < 1 ∧
      (∀ θ' ∈ Set.Ioo 0 θlow, ∀ e : ℝ, 0 < e →
        Impervious ({ M.homPreserve θ' with ε := e } : Model n)) ∧
      (∀ e : ℝ, 0 < e →
        (∀ θ' ∈ Set.Ioo θstar θup, Impervious ({ M.homPreserve θ' with ε := e } : Model n)) →
        ∀ θ' ∈ Set.Ioo θstar 1, Impervious ({ M.homPreserve θ' with ε := e } : Model n)) ∧
      (1 / 2 < M.b → ∃ e : ℝ, 0 < e ∧
        (∀ θ' ∈ Set.Ioo θstar θup, ¬ Impervious ({ M.homPreserve θ' with ε := e } : Model n)) ∧
        ∀ θ' ∈ Set.Ioo θup 1, Impervious ({ M.homPreserve θ' with ε := e } : Model n)) := by sorry

end SocialManip.Beliefs.Supplement
