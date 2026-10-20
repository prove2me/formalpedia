-- Prove2me | Theorems.Thm_ProRataUC_Sustain_lemma_1
-- name    : ProRataUC.Sustain.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:25.745607+00:00
-- url     : https://prove2.me/theorems/9aa0bab2-13dd-40be-b0c8-2a57bcebfb61
-- title:
--   Lemma 1, p. 14 — solo revenue R_j and the optimal solo fee in the four regions of π2j/π1j (with π1j > 0)
-- statement:
--   Assume the standing assumptions ($\lambda_2>\lambda_1>0$, $q\in(0,1)^2$, $q_1+q_2=1$, each $\pi_{i\cdot}$ a probability vector) and let $j$ be an artist with $\pi_{1j}>0$. Write $\rho_j=\pi_{2j}/\pi_{1j}$ and $R_j=\sup_r r\,d(j,r)$ for her solo revenue. Then:
--
--   1. If $\rho_j\in[0,\tfrac{q_1\lambda_1}{\lambda_2})$, the fee $\lambda_1\pi_{1j}$ is optimal, only type 1 users subscribe at that fee ($\lambda_2\pi_{2j}<\lambda_1\pi_{1j}$), and $R_j=q_1\lambda_1\pi_{1j}$.
--   2. If $\rho_j\in[\tfrac{q_1\lambda_1}{\lambda_2},\tfrac{\lambda_1}{\lambda_2})$, the fee $\lambda_2\pi_{2j}$ is optimal, both types subscribe at that fee ($\lambda_2\pi_{2j}\le\lambda_1\pi_{1j}$), and $R_j=\lambda_2\pi_{2j}$.
--   3. If $\rho_j\in[\tfrac{\lambda_1}{\lambda_2},\tfrac{\lambda_1}{\lambda_2q_2})$, the fee $\lambda_1\pi_{1j}$ is optimal, both types subscribe at that fee ($\lambda_1\pi_{1j}\le\lambda_2\pi_{2j}$), and $R_j=\lambda_1\pi_{1j}$.
--   4. If $\rho_j\in[\tfrac{\lambda_1}{\lambda_2q_2},\infty)$, the fee $\lambda_2\pi_{2j}$ is optimal, only type 2 users subscribe at that fee ($\lambda_1\pi_{1j}<\lambda_2\pi_{2j}$), and $R_j=q_2\lambda_2\pi_{2j}$.
--
--   In each case "the fee $f$ is optimal" means $f\,d(j,f)=R_j$, and type $i$ subscribes at fee $f$ exactly when $\lambda_i\pi_{ij}\ge f$. In short,
--   $$R_j=\begin{cases}q_1\lambda_1\pi_{1j},&j\in W,\\ \lambda_2\pi_{2j},&j\in Z,\\ \lambda_1\pi_{1j},&j\in Y,\\ q_2\lambda_2\pi_{2j},&j\in X.\end{cases}$$
--
--   This computes every artist's outside option, which is the minimum payment the platform must offer her; equations (10)–(11) and Lemmas 6–7 are built on it.
--
--   **Formalization Note** The paper never states $\pi_{1j}>0$, but its ratio $\pi_{2j}/\pi_{1j}$ presupposes it; Lean's division would give $0$ at $\pi_{1j}=0$, so the hypothesis is added for the artist at hand. "Only type 1 subscribes" is encoded by the strict inequality $\lambda_2\pi_{2j}<\lambda_1\pi_{1j}$ rather than by $d=q_1$, since $q_1=q_2$ is allowed. Lemma 1 does not use Assumption 1.
-- source:
--   Alaei, Makhdoumi, Malekian & Pekeč, Revenue-sharing allocation strategies for two-sided media platforms: Pro-rata vs. user-centric, submitted manuscript (SSRN 3645521), p. 14, Lemma 1 (proof p. 44)

import Mathlib
import Definitions.Def_ProRataUC_Sustain_Setting

namespace ProRataUC.Sustain
theorem lemma_1 {M : Type*} [Fintype M] (s : Setting M) (hs : s.Standing) (j : M)
    (hj : 0 < s.pi1 j) :
    (s.pi2 j / s.pi1 j ∈ Set.Ico 0 (s.q1 * s.lam1 / s.lam2) →
       s.lam1 * s.pi1 j * demand s j (s.lam1 * s.pi1 j) = soloRevenue s j ∧
       s.lam2 * s.pi2 j < s.lam1 * s.pi1 j ∧
       soloRevenue s j = s.q1 * s.lam1 * s.pi1 j) ∧
    (s.pi2 j / s.pi1 j ∈ Set.Ico (s.q1 * s.lam1 / s.lam2) (s.lam1 / s.lam2) →
       s.lam2 * s.pi2 j * demand s j (s.lam2 * s.pi2 j) = soloRevenue s j ∧
       s.lam2 * s.pi2 j ≤ s.lam1 * s.pi1 j ∧
       soloRevenue s j = s.lam2 * s.pi2 j) ∧
    (s.pi2 j / s.pi1 j ∈ Set.Ico (s.lam1 / s.lam2) (s.lam1 / (s.lam2 * s.q2)) →
       s.lam1 * s.pi1 j * demand s j (s.lam1 * s.pi1 j) = soloRevenue s j ∧
       s.lam1 * s.pi1 j ≤ s.lam2 * s.pi2 j ∧
       soloRevenue s j = s.lam1 * s.pi1 j) ∧
    (s.pi2 j / s.pi1 j ∈ Set.Ici (s.lam1 / (s.lam2 * s.q2)) →
       s.lam2 * s.pi2 j * demand s j (s.lam2 * s.pi2 j) = soloRevenue s j ∧
       s.lam1 * s.pi1 j < s.lam2 * s.pi2 j ∧
       soloRevenue s j = s.q2 * s.lam2 * s.pi2 j) := by sorry
end ProRataUC.Sustain
