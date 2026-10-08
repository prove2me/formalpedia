-- Prove2me | Theorems.Thm_RobustPCA_Recovery_sec_7_1_transfer
-- name    : RobustPCA.Recovery.sec_7_1_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:58.125204+00:00
-- url     : https://prove2.me/theorems/e4173a1a-e860-4db9-abc9-34d6d6aefeaf
-- title:
--   §7.1 — $\mathbb P_{\mathrm{Unif}(m)}(\text{Success})\ge\mathbb P_{\mathrm{Ber}(p)}(\text{Success})-\mathbb P_{\mathrm{Ber}(p)}(|\Omega|<m)$
-- statement:
--   Fix $\lambda\ge0$, matrices $L_0,S\in\mathbb R^{n\times n}$, an integer $0\le m\le n^2$ and $p\in[0,1]$. For a support $\Omega\subseteq[n]\times[n]$ let "Success" be the event that Principal Component Pursuit with weight $\lambda$ and input $L_0+\mathcal P_\Omega S$ has the unique solution $(L_0,\mathcal P_\Omega S)$. Write $\mathbb P_{\mathrm{Unif}(m)}$ for the uniform law on supports of cardinality $m$ and $\mathbb P_{\mathrm{Ber}(p)}$ for the law in which each entry belongs to $\Omega$ independently with probability $p$. Then
--   $$\mathbb P_{\mathrm{Unif}(m)}(\text{Success})\ \ge\ \mathbb P_{\mathrm{Ber}(p)}(\text{Success})-\mathbb P_{\mathrm{Ber}(p)}(|\Omega|<m).$$
--
--   This transfers a recovery guarantee proved for Bernoulli supports to the uniform model of Theorem 1.1.
--
--   **Formalization Note** "Success" is the paper's success event for the sparse component $\mathcal P_\Omega S$ with a fixed $S$, which is monotone in $\Omega$ by Theorem 2.2; the monotonicity is not assumed. The weight $\lambda$ is nonnegative.
-- source:
--   Candès, Li, Ma, Wright, Robust principal component analysis?, J. ACM 58(3) (2011), p. 31, §7.1, first display and the line after it

import Definitions.Def_RobustPCA_Recovery_Setup
open MatrixCompletion

namespace RobustPCA.Recovery

/-- §7.1, display, p. 31: for the event "PCP with input `L0 + 𝒫_Ω S` is exact",
`ℙ_Unif(m)(Success) ≥ ℙ_Ber(p)(Success) − ℙ_Ber(p)(|Ω| < m)`. -/
theorem sec_7_1_transfer {n : ℕ} (lam : ℝ) (L0 S : RealMatrix n n) (m : ℕ) (p : ℝ)
    (hlam : 0 ≤ lam) (hm : m ≤ n * n) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    fixedCardinalityEventProb m (fun Ω => IsPCPExact lam L0 (samplingProjection Ω S)) ≥
      bernoulliEventProb p (fun Ω => IsPCPExact lam L0 (samplingProjection Ω S)) -
        bernoulliEventProb p (fun Ω : Finset (Fin n × Fin n) => Ω.card < m) := by sorry

end RobustPCA.Recovery
