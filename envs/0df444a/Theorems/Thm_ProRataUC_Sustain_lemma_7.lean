-- Prove2me | Theorems.Thm_ProRataUC_Sustain_lemma_7
-- name    : ProRataUC.Sustain.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:24.824855+00:00
-- url     : https://prove2.me/theorems/84986413-bca5-4650-892d-b499f26f3836
-- title:
--   Lemma 7, p. 45 — user-centric sustains all artists iff the region-wise bounds on π2j/π1j hold for X, Y, Z
-- statement:
--   Assume the standing assumptions, Assumption 1 ($\lambda_1\ge\lambda_2q_2$) and $\pi_{1j}>0$ for every artist $j$, and write $\rho_j=\pi_{2j}/\pi_{1j}$. The platform is sustainable with the user-centric rule (some payout rate $\beta\in[0,1]$ pays every artist at least $R_j$) if and only if all of the following hold:
--
--   1. for all $j\in X$: $\displaystyle \rho_j\le\frac{q_1}{q_2}\,\frac{\lambda_1}{\lambda_2-\lambda_1}$;
--   2. for all $j\in Y$: $\rho_j\ge1$;
--   3. for all $j\in Z$: $\displaystyle \rho_j\le\frac{q_1}{\lambda_2/\lambda_1-q_2}$.
--
--   There is no condition on the region $W$. This is the user-centric half of the proof of Theorem 1.
--
--   **Formalization Note** Sustainability is the economic statement (existence of $\beta\in[0,1]$), not the paper's gloss "$\beta^{\mathrm{uc}}\le1$"; equation (11) links them. Assumption 1 is a hypothesis because the paper's proof uses $\max\{\lambda_1,\lambda_2q_2\}=\lambda_1$, and $\pi_{1j}>0$ is the paper's tacit assumption behind the ratio. The three printed conditions are kept as printed.
-- source:
--   Alaei, Makhdoumi, Malekian & Pekeč, Revenue-sharing allocation strategies for two-sided media platforms: Pro-rata vs. user-centric, submitted manuscript (SSRN 3645521), p. 45, Lemma 7 (Appendix A, proof of Theorem 1)

import Mathlib
import Definitions.Def_ProRataUC_Sustain_Setting

namespace ProRataUC.Sustain
theorem lemma_7 {M : Type*} [Fintype M] (s : Setting M) (hs : s.Standing) (hA : Assumption1 s)
    (hpos : ∀ j, 0 < s.pi1 j) :
    SustainableUC s ↔
      (∀ j ∈ regionX s, s.pi2 j / s.pi1 j ≤ s.q1 / s.q2 * (s.lam1 / (s.lam2 - s.lam1))) ∧
      (∀ j ∈ regionY s, 1 ≤ s.pi2 j / s.pi1 j) ∧
      (∀ j ∈ regionZ s, s.pi2 j / s.pi1 j ≤ s.q1 / (s.lam2 / s.lam1 - s.q2)) := by sorry
end ProRataUC.Sustain
