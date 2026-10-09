-- Prove2me | Theorems.Thm_StatComplexityDM_LowerBound_regret_gap_change_of_measure
-- name    : StatComplexityDM.LowerBound.regret_gap_change_of_measure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:12.078667+00:00
-- url     : https://prove2.me/theorems/5cee597c-d09e-47bb-9111-1659df9c36d5
-- title:
--   (132), p. 90 — for M ∈ M^∞_ε(M̄): |E_{p_M}[g^M − g^M̄] − E_{p_M̄}[g^M − g^M̄]| ≤ √(8ε(…)D²_H(P^M, P^M̄)) ≤ 4εD²_H + ½(…)
-- statement:
--   Let $\bar M\in\mathcal M$, $M\in\mathcal M^\infty_\varepsilon(\bar M)$ with $\varepsilon\ge0$, and let $p$ be an adaptive algorithm of horizon $T\ge1$ with average plays $p_M$ and $p_{\bar M}$ and history laws $\mathbb P^M$, $\mathbb P^{\bar M}$. Put $d=g^M-g^{\bar M}$ and $b=g^M+g^{\bar M}$, and $B=\mathbb E_{\pi\sim p_M}[b(\pi)]+\mathbb E_{\pi\sim p_{\bar M}}[b(\pi)]$. Then
--
--   $$
--   \bigl|\mathbb E_{\pi\sim p_M}[d(\pi)]-\mathbb E_{\pi\sim p_{\bar M}}[d(\pi)]\bigr|
--   \le\sqrt{8\varepsilon\,B\,D^2_{\mathrm H}(\mathbb P^M,\mathbb P^{\bar M})}
--   \le 4\varepsilon\,D^2_{\mathrm H}(\mathbb P^M,\mathbb P^{\bar M})+\tfrac12 B .
--   $$
--
--   It bounds how much the localized regret difference can change when the history law moves from $\bar M$ to $M$.
--
--   **Formalization Note** Decisions $\Pi$ and joint reward–observation outcomes $\mathcal R\times\mathcal O$ are finite alphabets (the finite-alphabet case of the paper's measurable setting, §2, p. 9); models and algorithm kernels are probability vectors and expectations are finite sums.
-- source:
--   arXiv:2112.13487v3, App. C.1.3, proof of Theorem 3.2, (132), p. 90

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_History

namespace StatComplexityDM.LowerBound

open FoundationsRL.GeneralDM

/-- App. C.1.3, (132), p. 90: the localized gap change of measure. -/
theorem regret_gap_change_of_measure {S Y : Type*} [Fintype S] [Fintype Y] [Nonempty S]
    (rew : Y → ℝ) (𝓜 : Set (S → Y → ℝ))
    (h𝓜 : ∀ m ∈ 𝓜, IsModel m)
    (piStar : (S → Y → ℝ) → S) (hpiStar : IsArgmaxSel rew piStar)
    (m mbar : S → Y → ℝ) (hmbar : mbar ∈ 𝓜)
    (ε : ℝ) (hε : 0 ≤ ε) (hm : m ∈ linfLocalized 𝓜 rew piStar mbar ε)
    (T : ℕ) (hT : 1 ≤ T)
    (alg : (t : Fin T) → History S Y t.val → S → ℝ)
    (halg : IsAlgorithm alg) :
    let diff : ℝ :=
      (∑ π : S, avgPlay m alg π *
         (rewardGap rew piStar m π - rewardGap rew piStar mbar π)) -
      (∑ π : S, avgPlay mbar alg π *
         (rewardGap rew piStar m π - rewardGap rew piStar mbar π))
    let total : ℝ :=
      (∑ π : S, avgPlay m alg π *
         (rewardGap rew piStar m π + rewardGap rew piStar mbar π)) +
      (∑ π : S, avgPlay mbar alg π *
         (rewardGap rew piStar m π + rewardGap rew piStar mbar π))
    |diff| ≤ Real.sqrt (8 * ε * total *
      hellingerSq (histLaw m alg) (histLaw mbar alg)) ∧
    Real.sqrt (8 * ε * total *
      hellingerSq (histLaw m alg) (histLaw mbar alg)) ≤
      4 * ε * hellingerSq (histLaw m alg) (histLaw mbar alg) +
        (1 / 2 : ℝ) * total := by sorry

end StatComplexityDM.LowerBound
