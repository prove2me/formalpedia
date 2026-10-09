-- Prove2me | Theorems.Thm_StatComplexityDM_LowerBound_sum_regret_ge_third_dec
-- name    : StatComplexityDM.LowerBound.sum_regret_ge_third_dec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:45.322755+00:00
-- url     : https://prove2.me/theorems/75f0abd2-30d7-4cf3-b4e1-262a479260bd
-- title:
--   App. C.1.3, p. 90, last display — if ε ≤ γ/(8C_T T): E_{p_M}[g^M] + E_{p_M̄}[g^M̄] ≥ ⅓·dec_γ (up to η)
-- statement:
--   Let $\mathcal M$ be a class of models with mean rewards in $[0,1]$, $\bar M\in\mathcal M$, $p$ an adaptive algorithm of horizon $T\ge1$, $\gamma>0$, and $0\le\varepsilon\le\gamma/(8C_TT)$ with $C_T=2^8\log\bigl(2T\wedge(V^{\bar M}(\mathcal M)\vee e)\bigr)$. Write $\mathrm{dec}_\gamma=\mathrm{dec}_\gamma(\mathcal M^\infty_\varepsilon(\bar M),\bar M)$. Then for every $\eta>0$ there is $M\in\mathcal M^\infty_\varepsilon(\bar M)$ with
--
--   $$
--   \mathbb E_{\pi\sim p_M}\bigl[g^M(\pi)\bigr]+\mathbb E_{\pi\sim p_{\bar M}}\bigl[g^{\bar M}(\pi)\bigr]\ge\tfrac13\,(\mathrm{dec}_\gamma-\eta).
--   $$
--
--   Since $T\,\mathbb E_{\pi\sim p_M}[g^M(\pi)]$ is the expected regret of $p$ on $M$, one of the two models has expected regret at least $\tfrac16(\mathrm{dec}_\gamma-\eta)T$; this is the last step before Theorem 3.2.
--
--   **Formalization Note** Decisions $\Pi$ and joint reward–observation outcomes $\mathcal R\times\mathcal O$ are finite alphabets (the finite-alphabet case of the paper's measurable setting, §2, p. 9); models and algorithm kernels are probability vectors and expectations are finite sums. The $\eta$ replaces the page's attained supremum (the limit sequence of (129)). $C_T$ carries the cutoff $\vee e$ required by Lemma A.13 (98); see the history-bound item.
-- source:
--   arXiv:2112.13487v3, App. C.1.3, proof of Theorem 3.2, p. 90 (last display)

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_History
import Definitions.Def_FoundationsRL_GeneralDM_DEC

namespace StatComplexityDM.LowerBound

open FoundationsRL.GeneralDM

/-- App. C.1.3, proof of Theorem 3.2, p. 90, last display: if `ε ≤ γ/(8 C_T T)`, the model of
(129) satisfies `E_{π∼p_M}[g^M(π)] + E_{π∼p_{M̄}}[g^{M̄}(π)] ≥ ⅓ dec_γ` (up to any `η > 0`). -/
theorem sum_regret_ge_third_dec {S Y : Type*} [Fintype S] [Fintype Y]
    [Nonempty S] [DecidableEq Y] (rew : Y → ℝ) (𝓜 : Set (S → Y → ℝ))
    (h𝓜 : ∀ m ∈ 𝓜, IsModel m)
    (piStar : (S → Y → ℝ) → S) (hpiStar : IsArgmaxSel rew piStar)
    (hF : ∀ m ∈ 𝓜, ∀ π, 0 ≤ fM rew m π ∧ fM rew m π ≤ 1)
    (mbar : S → Y → ℝ) (hmbar : mbar ∈ 𝓜)
    (T : ℕ) (hT : 1 ≤ T)
    (alg : (t : Fin T) → History S Y t.val → S → ℝ)
    (halg : IsAlgorithm alg) (ε γ η : ℝ) (hε : 0 ≤ ε) (hγ : 0 < γ)
    (hεγ : ε ≤ γ / (8 * historyConstant 𝓜 mbar T * (T : ℝ))) (hη : 0 < η) :
    ∃ m ∈ linfLocalized 𝓜 rew piStar mbar ε,
      (1 / 3 : ℝ) * (decGf (linfLocalized 𝓜 rew piStar mbar ε) rew piStar γ mbar - η) ≤
        (∑ π : S, avgPlay m alg π * rewardGap rew piStar m π) +
          ∑ π : S, avgPlay mbar alg π * rewardGap rew piStar mbar π := by sorry

end StatComplexityDM.LowerBound
