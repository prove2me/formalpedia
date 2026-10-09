-- Prove2me | Theorems.Thm_StatComplexityDM_MAB_ber_family_subset_localized
-- name    : StatComplexityDM.MAB.ber_family_subset_localized
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:08.561431+00:00
-- url     : https://prove2.me/theorems/ca5fb86f-47f7-4fa2-ac7d-a059ab49196a
-- title:
--   Proof of Proposition 5.3, p. 32 — the hard family lies in the L∞-localized class: M′ ⊆ M^∞_Δ(M̄)
-- statement:
--   Consider the $A$-armed Bernoulli bandit with $A \ge 2$ and an optimal-arm selector $M \mapsto \pi_M$. For $\Delta \in (0, \tfrac12)$ let $M_i(\pi) = \mathrm{Ber}(\tfrac12 + \Delta\, \mathbb{I}\{\pi = i\})$ and $\overline{M}(\pi) = \mathrm{Ber}(\tfrac12)$. Then
--   $$
--   \{M_1, \dots, M_A\} \subseteq \mathcal{M}^\infty_\Delta(\overline{M}),
--   $$
--   where $\mathcal{M}^\infty_\varepsilon(\overline{M}) = \{M \in \mathcal{M} : |g^M(\pi) - g^{\overline{M}}(\pi)| \le \varepsilon\ \forall \pi\}$, $g^M(\pi) = f^M(\pi_M) - f^M(\pi)$, and $\mathcal{M}$ is the class of all Bernoulli bandits.
--
--   Localization is what makes the DEC lower bound usable in the paper's regret lower bound (Theorem 3.2), which takes the DEC of a localized class.
--
--   **Formalization Note** $\overline{M}$ has every arm optimal; the statement holds for every choice of $\pi_{\overline{M}}$, since $g^{\overline{M}} \equiv 0$. The class is the Bernoulli subclass of the paper's $\mathcal{M}$, which makes the inclusion stronger.
-- source:
--   arXiv:2112.13487v3, proof of Proposition 5.3, p. 32

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_Core
import Definitions.Def_StatComplexityDM_MAB_Bernoulli

namespace StatComplexityDM.MAB

open FoundationsRL.GeneralDM

/-- Proof of Proposition 5.3 (arXiv:2112.13487v3, p. 32): the hard family
`M′ = {M_1, …, M_A}`, `M_i(π) = Ber(1/2 + Δ · I{π = i})`, lies in the `L∞`-localized class
`M^∞_Δ(M̄)` of (12) around `M̄(π) = Ber(1/2)`, inside the class of all Bernoulli bandits, for
`Δ ∈ (0, 1/2)` and every selector `piStar` of maximizers of the mean reward. -/
theorem ber_family_subset_localized (A : ℕ) (hA : 2 ≤ A)
    (piStar : (Fin A → Bool → ℝ) → Fin A)
    (hpiStar : StatComplexityDM.LowerBound.IsArgmaxSel berRew piStar) (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 2) :
    Set.range (berFamily A Δ) ⊆
      StatComplexityDM.LowerBound.linfLocalized (bernoulliBandits A) berRew piStar (fun _ => ber (1 / 2)) Δ := by sorry

end StatComplexityDM.MAB
