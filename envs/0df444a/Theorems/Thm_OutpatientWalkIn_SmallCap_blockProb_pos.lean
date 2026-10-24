-- Prove2me | Theorems.Thm_OutpatientWalkIn_SmallCap_blockProb_pos
-- name    : OutpatientWalkIn.SmallCap.blockProb_pos
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-23T12:52:25.126442+00:00
-- url     : https://prove2.me/theorems/feb1c90c-39bb-456c-a7a8-52244045c373
-- title:
--   Corollary C.1, Online Appendix p. 7 — the blocking probability $\pi(\delta,\mu_S)$ is positive
-- statement:
--   Let $\lambda>0$, $\mu_S>0$ and $\delta\ge0$. Consider the observable appointment queue, the $M/D/1/K-1+p$ queue with Poisson arrival rate $\lambda$, deterministic service at rate $\mu_S$, $K=\lceil\delta\mu_S\rceil$ and $p=\delta\mu_S+1-K$, and put $\rho=\lambda/\mu_S$. Its blocking probability, the probability that an arriving patient finds the delay above the threshold $\delta$ and does not join (Corollary C.1),
--   $$\pi(\delta,\mu_S)=1-\frac{1}{q_0+\rho},$$
--   where $q_0$ is the departure-epoch probability of an empty system from (27) (or from §C.1 when $p=1$), is strictly positive:
--   $$\pi(\delta,\mu_S)>0.$$
--
--   A finite buffer always turns away some Poisson arrivals. Positivity is what makes the guard $p_W+p_B>0$ in the observable equilibrium consistent with condition (8), $p_W+p_B=\pi(\delta,\mu_S)$. In the existence proof of Proposition 1 it is needed in Regime SnB, where $p_B=\pi(R/C_D,\mu_S)$, and in Regime SnW, where $p_W=\pi(\delta,\mu_S)$.
--
--   **Formalization Note** The paper treats $\pi$ as a probability and uses its positivity implicitly. The statement is about the explicit Brun–Garcia formula: $a_j$, $b_j$, $a'_K$ and $q_0$ as defined in `Def_OutpatientWalkIn_SmallCap_MD1Queue`. A numerical evaluation of that formula gives, for example, $\pi(0,\mu_S)=\rho/(1+\rho)$, and positive values decreasing in $\delta$ for several $(\lambda,\mu_S)$.
-- source:
--   Liu, van Jaarsveld, Wang, Xiao, Managing Outpatient Service with Strategic Walk-ins, SSRN 3558209 (version of 2022-07-05), Online Appendix p. 7, Corollary C.1 (π(δ, µ_S) as the blocking probability of the M/D/1/K−1+p queue); used in the proof of Proposition 1, Online Appendix D.3, p. 10

import Mathlib
import Definitions.Def_OutpatientWalkIn_SmallCap_MD1Queue

namespace OutpatientWalkIn.SmallCap
theorem blockProb_pos (lam : ℝ) (hlam : 0 < lam) (μS : ℝ) (hμS : 0 < μS) (δ : ℝ) (hδ : 0 ≤ δ) :
    0 < blockProb lam δ μS := by sorry
end OutpatientWalkIn.SmallCap
