-- Prove2me | Theorems.Thm_ProRataUC_Sustain_eq_11
-- name    : ProRataUC.Sustain.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:23.203188+00:00
-- url     : https://prove2.me/theorems/985a74bb-3b03-4e6c-a80a-88729a46a7a4
-- title:
--   Eq. (11), p. 16 — β^uc is the least payout rate at which user-centric pays every artist at least R_j
-- statement:
--   Assume the standing assumptions, Assumption 1 ($\lambda_1\ge\lambda_2q_2$), at least one artist, and $\pi_{1j}>0$ for every artist $j$. Let $p^{\mathrm{uc}}_j(\beta)$ be the user-centric payment of Definition 2 with all artists on the platform and both user types subscribing, and let
--   $$\beta^{\mathrm{uc}}=\frac1{\lambda_1}\max_{j\in\mathcal M}\frac{R_j}{q_1\pi_{1j}+q_2\pi_{2j}}.$$
--   Then for every real $\beta$,
--   $$\bigl(\forall j\in\mathcal M:\ R_j\le p^{\mathrm{uc}}_j(\beta)\bigr)\iff \beta^{\mathrm{uc}}\le\beta.$$
--
--   So $\beta^{\mathrm{uc}}$ is exactly the smallest payout rate under which the user-centric rule keeps every artist on the platform.
--
--   **Formalization Note** The payment is the general Definition 2 with $\mathrm{Fee}=\min(\lambda_1\sum_j\pi_{1j},\lambda_2\sum_j\pi_{2j})$ and the sums as printed; the paper's simplified form $\beta\lambda_1(q_1\pi_{1j}+q_2\pi_{2j})$ is part of what is to be proved. Assumption 1, $\pi_{1j}>0$ and `[Nonempty M]` are added for the same reasons as in equation (10). Only the first line of (11) is stated.
-- source:
--   Alaei, Makhdoumi, Malekian & Pekeč, Revenue-sharing allocation strategies for two-sided media platforms: Pro-rata vs. user-centric, submitted manuscript (SSRN 3645521), p. 16, Eq. (11) (first line)

import Mathlib
import Definitions.Def_ProRataUC_Sustain_Setting

namespace ProRataUC.Sustain
theorem eq_11 {M : Type*} [Fintype M] [Nonempty M] (s : Setting M) (hs : s.Standing)
    (hA : Assumption1 s) (hpos : ∀ j, 0 < s.pi1 j) (β : ℝ) :
    (∀ j, soloRevenue s j ≤ userCentricPay s β j) ↔ betaUC s ≤ β := by sorry
end ProRataUC.Sustain
