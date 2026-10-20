-- Prove2me | Theorems.Thm_ProRataUC_Sustain_lemma_6
-- name    : ProRataUC.Sustain.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:28.755774+00:00
-- url     : https://prove2.me/theorems/c2f8e99f-b806-45db-98cf-3e7e23c1cec0
-- title:
--   Lemma 6, p. 45 — pro-rata sustains all artists iff the four region-wise bounds on π2j/π1j hold
-- statement:
--   Assume the standing assumptions, Assumption 1 ($\lambda_1\ge\lambda_2q_2$) and $\pi_{1j}>0$ for every artist $j$, and write $\rho_j=\pi_{2j}/\pi_{1j}$. The platform is sustainable with the pro-rata rule (some payout rate $\beta\in[0,1]$ pays every artist at least $R_j$) if and only if all of the following hold:
--
--   1. for all $j\in X$: $\displaystyle \rho_j\le\frac{q_1\lambda_1}{\lambda_2q_2^2}\Bigl(\frac{\lambda_1}{\lambda_2-\lambda_1}\Bigr)$;
--   2. for all $j\in Y$: $\rho_j\ge1$;
--   3. for all $j\in Z$: $\displaystyle \rho_j\le\frac{q_1\lambda_1^2}{\lambda_2^2q_2+\lambda_1\lambda_2(q_1-q_2)}$;
--   4. for all $j\in W$: $\displaystyle \rho_j\ge\frac{q_1(\lambda_2-\lambda_1)}{\lambda_2}$.
--
--   Here $W,Z,Y,X$ are the regions $[0,\tfrac{q_1\lambda_1}{\lambda_2})$, $[\tfrac{q_1\lambda_1}{\lambda_2},\tfrac{\lambda_1}{\lambda_2})$, $[\tfrac{\lambda_1}{\lambda_2},\tfrac{\lambda_1}{\lambda_2q_2})$, $[\tfrac{\lambda_1}{\lambda_2q_2},\infty)$ of $\rho_j$. This is the pro-rata half of the proof of Theorem 1: it turns sustainability into one condition per region.
--
--   **Formalization Note** The paper glosses sustainability as "$\beta^{\mathrm{pr}}\le1$"; here it is the economic statement (existence of $\beta\in[0,1]$ with every payment at least $R_j$), and equation (10) links the two. The paper says "for a given $\lambda$ and $q$", but its proof uses $\max\{\lambda_1,\lambda_2q_2\}=\lambda_1$, i.e. Assumption 1, which is therefore a hypothesis. $\pi_{1j}>0$ is the paper's tacit assumption behind the ratio. The bound for $X$ is kept in the printed product form.
-- source:
--   Alaei, Makhdoumi, Malekian & Pekeč, Revenue-sharing allocation strategies for two-sided media platforms: Pro-rata vs. user-centric, submitted manuscript (SSRN 3645521), p. 45, Lemma 6 (Appendix A, proof of Theorem 1)

import Mathlib
import Definitions.Def_ProRataUC_Sustain_Setting

namespace ProRataUC.Sustain
theorem lemma_6 {M : Type*} [Fintype M] (s : Setting M) (hs : s.Standing) (hA : Assumption1 s)
    (hpos : ∀ j, 0 < s.pi1 j) :
    SustainablePR s ↔
      (∀ j ∈ regionX s, s.pi2 j / s.pi1 j ≤
         s.q1 * s.lam1 / (s.lam2 * s.q2 ^ 2) * (s.lam1 / (s.lam2 - s.lam1))) ∧
      (∀ j ∈ regionY s, 1 ≤ s.pi2 j / s.pi1 j) ∧
      (∀ j ∈ regionZ s, s.pi2 j / s.pi1 j ≤
         s.q1 * s.lam1 ^ 2 / (s.lam2 ^ 2 * s.q2 + s.lam1 * s.lam2 * (s.q1 - s.q2))) ∧
      (∀ j ∈ regionW s, s.q1 * (s.lam2 - s.lam1) / s.lam2 ≤ s.pi2 j / s.pi1 j) := by sorry
end ProRataUC.Sustain
