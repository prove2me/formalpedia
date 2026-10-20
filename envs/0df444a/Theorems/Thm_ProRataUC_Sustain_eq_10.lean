-- Prove2me | Theorems.Thm_ProRataUC_Sustain_eq_10
-- name    : ProRataUC.Sustain.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:22.542636+00:00
-- url     : https://prove2.me/theorems/9893512b-ab71-48ec-b003-7ec17b7b0784
-- title:
--   Eq. (10), p. 16 — β^pr is the least payout rate at which pro-rata pays every artist at least R_j
-- statement:
--   Assume the standing assumptions, Assumption 1 ($\lambda_1\ge\lambda_2q_2$), at least one artist, and $\pi_{1j}>0$ for every artist $j$. Let $p^{\mathrm{pr}}_j(\beta)$ be the pro-rata payment of Definition 1 with all artists on the platform and both user types subscribing, and let
--   $$\beta^{\mathrm{pr}}=\frac{q_1\lambda_1+q_2\lambda_2}{\lambda_1}\max_{j\in\mathcal M}\frac{R_j}{q_1\lambda_1\pi_{1j}+q_2\lambda_2\pi_{2j}}.$$
--   Then for every real $\beta$,
--   $$\bigl(\forall j\in\mathcal M:\ R_j\le p^{\mathrm{pr}}_j(\beta)\bigr)\iff \beta^{\mathrm{pr}}\le\beta.$$
--
--   So $\beta^{\mathrm{pr}}$ is exactly the smallest payout rate under which pro-rata keeps every artist on the platform, which is how the paper introduces (10).
--
--   **Formalization Note** The payment is the general Definition 1 with $\mathrm{Fee}=\min(\lambda_1\sum_j\pi_{1j},\lambda_2\sum_j\pi_{2j})$ and the sums as printed; the paper's simplified form $\beta\lambda_1(q_1\lambda_1\pi_{1j}+q_2\lambda_2\pi_{2j})/(q_1\lambda_1+q_2\lambda_2)$ is part of what is to be proved. Assumption 1 is added because the paper adopts it on p. 16 for what follows and its derivation uses $\mathrm{Rev}=\lambda_1$. $\pi_{1j}>0$ is the paper's tacit assumption behind the ratio $\pi_{2j}/\pi_{1j}$. `[Nonempty M]` is needed for the maximum and follows from $\sum_j\pi_{1j}=1$. Only the first line of (10) is stated; its second line is a rewriting by Lemma 1.
-- source:
--   Alaei, Makhdoumi, Malekian & Pekeč, Revenue-sharing allocation strategies for two-sided media platforms: Pro-rata vs. user-centric, submitted manuscript (SSRN 3645521), p. 16, Eq. (10) (first line)

import Mathlib
import Definitions.Def_ProRataUC_Sustain_Setting

namespace ProRataUC.Sustain
theorem eq_10 {M : Type*} [Fintype M] [Nonempty M] (s : Setting M) (hs : s.Standing)
    (hA : Assumption1 s) (hpos : ∀ j, 0 < s.pi1 j) (β : ℝ) :
    (∀ j, soloRevenue s j ≤ proRataPay s β j) ↔ betaPR s ≤ β := by sorry
end ProRataUC.Sustain
