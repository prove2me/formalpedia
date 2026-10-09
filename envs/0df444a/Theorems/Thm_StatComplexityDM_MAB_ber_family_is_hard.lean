-- Prove2me | Theorems.Thm_StatComplexityDM_MAB_ber_family_is_hard
-- name    : StatComplexityDM.MAB.ber_family_is_hard
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:48.221988+00:00
-- url     : https://prove2.me/theorems/ab9e6010-70fa-4162-84c8-611ad2834e6a
-- title:
--   Proof of Proposition 5.3, p. 32 — M_i(π) = Ber(1/2 + Δ·I{π = i}) is a (Δ, 3Δ², 0)-family around Ber(1/2)
-- statement:
--   Consider the $A$-armed Bernoulli bandit, $A \ge 2$, with reward equal to the outcome, and let $M \mapsto \pi_M$ select an optimal arm of every model. For $\Delta \in (0, \tfrac12)$ define
--   $$
--   M_i(\pi) = \mathrm{Ber}\bigl(\tfrac12 + \Delta\, \mathbb{I}\{\pi = i\}\bigr), \qquad i \in [A], \qquad \overline{M}(\pi) = \mathrm{Ber}(\tfrac12).
--   $$
--   Then $\{M_1, \dots, M_A\}$ is a $(\Delta, 3\Delta^2, 0)$-family with respect to $\overline{M}$ (Definition 5.1), with $N = A$.
--
--   The witnesses are $u_i(\pi) = v_i(\pi) = \mathbb{I}\{\pi = i\}$: arm $i$ is the unique optimal arm of $M_i$, every other arm has regret $\Delta$ under $M_i$, and $M_i$ differs from $\overline{M}$ only at arm $i$, by at most $3\Delta^2$ in squared Hellinger distance (Lemma A.7). This is the hard instance behind the $\sqrt{AT}$ regret lower bound for bandits.
--
--   **Formalization Note** The page checks $\sum_\pi u_i(\pi) = 1$; Definition 5.1 asks for $\sum_i u_i(\pi) \le N/2$ and $\sum_i v_i(\pi) \le 1$, which is what is stated (both hold, since $\sum_i \mathbb{I}\{\pi = i\} = 1 \le A/2$). Bernoulli outcomes encode the reward set $\{0,1\} \subseteq [0,1]$.
-- source:
--   arXiv:2112.13487v3, proof of Proposition 5.3, p. 32

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_MAB_HardFamily
import Definitions.Def_StatComplexityDM_MAB_Bernoulli

namespace StatComplexityDM.MAB

open FoundationsRL.GeneralDM

/-- The hard family of the proof of Proposition 5.3 (arXiv:2112.13487v3, p. 32): for `A ≥ 2`
arms and `Δ ∈ (0, 1/2)`, the models `M_i(π) = Ber(1/2 + Δ · I{π = i})`, `i ∈ [A]`, form a
`(Δ, 3Δ², 0)`-family (Definition 5.1) with respect to `M̄(π) = Ber(1/2)`, for every selector
`piStar` of maximizers of the mean reward. -/
theorem ber_family_is_hard (A : ℕ) (hA : 2 ≤ A) (piStar : (Fin A → Bool → ℝ) → Fin A)
    (hpiStar : StatComplexityDM.LowerBound.IsArgmaxSel berRew piStar) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 2) :
    IsHardFamily (bernoulliBandits A) berRew piStar (fun _ => ber (1 / 2))
      (berFamily A Δ) Δ (3 * Δ ^ 2) 0 := by sorry

end StatComplexityDM.MAB
