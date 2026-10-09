-- Prove2me | Theorems.Thm_StatComplexityDM_LowerBound_dec_at_average_play
-- name    : StatComplexityDM.LowerBound.dec_at_average_play
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:33.576203+00:00
-- url     : https://prove2.me/theorems/ac575b1f-2518-45f6-b240-1f35db466ff0
-- title:
--   (129), p. 90 — some M ∈ M^∞_ε(M̄) has E_{p_M̄}[g^M] ≥ γ·E_{p_M̄}[D²_H(M(π), M̄(π))] + dec_γ − η
-- statement:
--   Let $\mathcal M$ be a class of models with mean rewards in $[0,1]$, $\bar M\in\mathcal M$, $p$ an adaptive algorithm of horizon $T\ge1$, $\gamma>0$ and $\varepsilon\ge0$. Let $p_{\bar M}$ be the expected average play of $p$ under $\bar M$, and write $\mathrm{dec}_\gamma=\mathrm{dec}_\gamma(\mathcal M^\infty_\varepsilon(\bar M),\bar M)$, where
--
--   $$
--   \mathrm{dec}_\gamma(\mathcal M',\bar M)=\inf_{q\in\Delta(\Pi)}\sup_{M\in\mathcal M'}\mathbb E_{\pi\sim q}\bigl[f^M(\pi_M)-f^M(\pi)-\gamma D^2_{\mathrm H}(M(\pi),\bar M(\pi))\bigr].
--   $$
--
--   Then for every $\eta>0$ there is $M\in\mathcal M^\infty_\varepsilon(\bar M)$ with
--
--   $$
--   \mathbb E_{\pi\sim p_{\bar M}}\bigl[f^M(\pi_M)-f^M(\pi)\bigr]\ge\gamma\,\mathbb E_{\pi\sim p_{\bar M}}\bigl[D^2_{\mathrm H}(M(\pi),\bar M(\pi))\bigr]+\mathrm{dec}_\gamma-\eta .
--   $$
--
--   This is the definition of the decision-estimation coefficient evaluated at the distribution the algorithm actually induces under the reference model; it selects the alternative model of the lower-bound argument.
--
--   **Formalization Note** Decisions $\Pi$ and joint reward–observation outcomes $\mathcal R\times\mathcal O$ are finite alphabets (the finite-alphabet case of the paper's measurable setting, §2, p. 9); models and algorithm kernels are probability vectors and expectations are finite sums. The page lets $M$ attain the supremum "or consider a limit sequence"; the $\eta>0$ is that limit sequence. The page writes $\mathcal M_\varepsilon(\bar M)$ in (129) for the class $\mathcal M^\infty_\varepsilon(\bar M)$ it has just introduced.
-- source:
--   arXiv:2112.13487v3, App. C.1.3, proof of Theorem 3.2, (129), p. 90

import Mathlib
import Definitions.Def_StatComplexityDM_LowerBound_History
import Definitions.Def_FoundationsRL_GeneralDM_DEC

namespace StatComplexityDM.LowerBound

open FoundationsRL.GeneralDM

/-- App. C.1.3, (129), p. 90: the DEC payoff at the reference average play. -/
theorem dec_at_average_play {S Y : Type*} [Fintype S] [Fintype Y]
    [Nonempty S] (rew : Y → ℝ) (𝓜 : Set (S → Y → ℝ))
    (h𝓜 : ∀ m ∈ 𝓜, IsModel m)
    (piStar : (S → Y → ℝ) → S) (hpiStar : IsArgmaxSel rew piStar)
    (hF : ∀ m ∈ 𝓜, ∀ π, 0 ≤ fM rew m π ∧ fM rew m π ≤ 1)
    (mbar : S → Y → ℝ) (hmbar : mbar ∈ 𝓜)
    (T : ℕ) (hT : 1 ≤ T)
    (alg : (t : Fin T) → History S Y t.val → S → ℝ)
    (halg : IsAlgorithm alg) (ε γ η : ℝ) (hε : 0 ≤ ε) (hγ : 0 < γ) (hη : 0 < η) :
    ∃ m ∈ linfLocalized 𝓜 rew piStar mbar ε,
      γ * (∑ π : S, avgPlay mbar alg π * hellingerSq (m π) (mbar π)) +
        decGf (linfLocalized 𝓜 rew piStar mbar ε) rew piStar γ mbar - η ≤
          ∑ π : S, avgPlay mbar alg π * rewardGap rew piStar m π := by sorry

end StatComplexityDM.LowerBound
