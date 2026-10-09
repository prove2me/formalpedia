-- Prove2me | Theorems.Thm_StatComplexityDM_MAB_mab_localized_dec_lower_bound
-- name    : StatComplexityDM.MAB.mab_localized_dec_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:22.277492+00:00
-- url     : https://prove2.me/theorems/b7bae0a0-5689-491d-bda2-0659ae370d3a
-- title:
--   Proposition 5.3, p. 32 — A-armed bandit, M̄(π) = Ber(1/2): dec_γ(M^∞_{ε_γ}(M̄), M̄) ≥ 2⁻⁶·A/γ for γ ≥ A/3, ε_γ = A/(12γ)
-- statement:
--   Consider the multi-armed bandit problem with $A \ge 2$ actions $\Pi = [A]$ and rewards in $[0,1]$, and the reference model $\overline{M}(\pi) = \mathrm{Ber}(\tfrac12)$ for every arm. For every $\gamma \ge A/3$, with $\varepsilon_\gamma = \frac{A}{12\gamma}$,
--   $$
--   \mathsf{dec}_\gamma\bigl(\mathcal{M}^\infty_{\varepsilon_\gamma}(\overline{M}), \overline{M}\bigr) \ge 2^{-6} \cdot \frac{A}{\gamma},
--   $$
--   where $\mathsf{dec}_\gamma(\mathcal{M}, \overline{M}) = \inf_{p \in \Delta(\Pi)} \sup_{M \in \mathcal{M}} \mathbb{E}_{\pi \sim p}[f^M(\pi_M) - f^M(\pi) - \gamma D^2_{\mathrm{H}}(M(\pi), \overline{M}(\pi))]$ is the Decision-Estimation Coefficient and $\mathcal{M}^\infty_{\varepsilon}(\overline{M})$ is the $L_\infty$-localized class (12).
--
--   Combined with the paper's in-expectation lower bound (Theorem 3.2), this yields the $\Omega(\sqrt{AT})$ minimax regret lower bound for multi-armed bandits, matching the DEC upper bounds of Propositions 5.1 and 5.2 up to constants.
--
--   **Formalization Note** The model class is the Bernoulli bandits (reward distributions supported on $\{0,1\}$), a subclass of the paper's class of all distributions on $[0,1]$; since the localized class shrinks and the DEC decreases when passing to a subclass, this bound implies the paper's. The bound holds for every selector $\pi_M$ of optimal arms. The constant $2^{-6}$ is the page's; its proof yields $1/48$.
-- source:
--   arXiv:2112.13487v3, Proposition 5.3, p. 32

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_DEC
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_MAB_Bernoulli

namespace StatComplexityDM.MAB

open FoundationsRL.GeneralDM

/-- Proposition 5.3 (arXiv:2112.13487v3, p. 32): for the multi-armed bandit with `A ≥ 2` arms,
rewards in `[0, 1]` and reference model `M̄(π) = Ber(1/2)`,
`dec_γ(M^∞_{ε_γ}(M̄), M̄) ≥ 2⁻⁶ · A/γ` for all `γ ≥ A/3`, where `ε_γ = A/(12γ)`.
The class is the Bernoulli bandits (a subclass of the paper's, which makes the bound stronger),
`dec_γ` is `decGf` (2) and `M^∞_ε(M̄)` is `linfLocalized` (12); the bound holds for every selector
`piStar` of maximizers of the mean reward. -/
theorem mab_localized_dec_lower_bound (A : ℕ) (hA : 2 ≤ A)
    (piStar : (Fin A → Bool → ℝ) → Fin A) (hpiStar : StatComplexityDM.LowerBound.IsArgmaxSel berRew piStar)
    (γ : ℝ) (hγ : (A : ℝ) / 3 ≤ γ) :
    (2 : ℝ) ^ (-6 : ℤ) * ((A : ℝ) / γ) ≤
      decGf (StatComplexityDM.LowerBound.linfLocalized (bernoulliBandits A) berRew piStar (fun _ => ber (1 / 2))
          ((A : ℝ) / (12 * γ)))
        berRew piStar γ (fun _ => ber (1 / 2)) := by sorry

end StatComplexityDM.MAB
