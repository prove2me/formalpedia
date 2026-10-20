-- Prove2me | Theorems.Thm_ProRataUC_Sustain_theorem_1
-- name    : ProRataUC.Sustain.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:27.990051+00:00
-- url     : https://prove2.me/theorems/4627c558-f40c-494a-85d7-eb20c28eee51
-- title:
--   Theorem 1, p. 17 — under Assumption 1, pro-rata (user-centric) sustains all artists iff every π2j/π1j lies in the printed union of two intervals
-- statement:
--   Consider a streaming platform with two user types (usage rates $\lambda_2>\lambda_1>0$, masses $q_1,q_2\in(0,1)$ with $q_1+q_2=1$) and a finite set $\mathcal M$ of artists, where $\pi_{ij}\ge0$ is the probability that a type $i$ user wants artist $j$ and $\sum_j\pi_{ij}=1$. Suppose Assumption 1, $\lambda_1\ge\lambda_2q_2$, holds and $\pi_{1j}>0$ for every artist. The platform is *sustainable* with a revenue allocation rule if some payout rate $\beta\in[0,1]$ pays every artist at least her solo revenue $R_j=\max_r r\,d(j,r)$.
--
--   **(a)** The platform is sustainable with the pro-rata rule if and only if, for all $j\in\mathcal M$,
--   $$\frac{\pi_{2j}}{\pi_{1j}}\in\Bigl[\frac{q_1(\lambda_2-\lambda_1)}{\lambda_2},\ \frac{q_1\lambda_1^2}{\lambda_2^2q_2+\lambda_1\lambda_2(q_1-q_2)}\Bigr]\ \cup\ \Bigl[1,\ \frac{q_1\lambda_1^2}{\lambda_2q_2^2(\lambda_2-\lambda_1)}\Bigr].$$
--
--   **(b)** The platform is sustainable with the user-centric rule if and only if, for all $j\in\mathcal M$,
--   $$\frac{\pi_{2j}}{\pi_{1j}}\in\Bigl[0,\ \frac{q_1\lambda_1}{\lambda_2-q_2\lambda_1}\Bigr]\ \cup\ \Bigl[1,\ \frac{q_1\lambda_1}{q_2(\lambda_2-\lambda_1)}\Bigr].$$
--
--   The theorem shows that each rule can keep all artists exactly when every artist's ratio of heavy-user to light-user listening falls in two explicit windows, and it locates the difference between the rules: pro-rata tolerates artists favoured by heavy users up to a larger ratio, while user-centric also keeps artists favoured by light users.
--
--   **Formalization Note** Payments are Definitions 1–2 with all artists on the platform and both user types subscribing, and $R_j$ is the supremum of $r\,d(j,r)$ over all real prices with the printed four-case demand. The hypothesis $\pi_{1j}>0$ is added: the paper's ratio presupposes it, and Lean's division would assign the ratio $0$ to an artist with $\pi_{1j}=0<\pi_{2j}$, making part (b) false for her. The intervals are closed as printed; the first interval in (a) is empty when $\lambda_2>2\lambda_1$, which is the correct reading of the printed statement.
-- source:
--   Alaei, Makhdoumi, Malekian & Pekeč, Revenue-sharing allocation strategies for two-sided media platforms: Pro-rata vs. user-centric, submitted manuscript (SSRN 3645521), p. 17, Theorem 1 (proof pp. 45–46)

import Mathlib
import Definitions.Def_ProRataUC_Sustain_Setting

namespace ProRataUC.Sustain
theorem theorem_1 {M : Type*} [Fintype M] (s : Setting M) (hs : s.Standing) (hA : Assumption1 s)
    (hpos : ∀ j, 0 < s.pi1 j) :
    (SustainablePR s ↔ ∀ j, s.pi2 j / s.pi1 j ∈
        Set.Icc (s.q1 * (s.lam2 - s.lam1) / s.lam2)
          (s.q1 * s.lam1 ^ 2 / (s.lam2 ^ 2 * s.q2 + s.lam1 * s.lam2 * (s.q1 - s.q2))) ∪
        Set.Icc 1 (s.q1 * s.lam1 ^ 2 / (s.lam2 * s.q2 ^ 2 * (s.lam2 - s.lam1)))) ∧
    (SustainableUC s ↔ ∀ j, s.pi2 j / s.pi1 j ∈
        Set.Icc 0 (s.q1 * s.lam1 / (s.lam2 - s.q2 * s.lam1)) ∪
        Set.Icc 1 (s.q1 * s.lam1 / (s.q2 * (s.lam2 - s.lam1)))) := by sorry
end ProRataUC.Sustain
