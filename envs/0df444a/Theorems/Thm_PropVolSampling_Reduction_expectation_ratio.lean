-- Prove2me | Theorems.Thm_PropVolSampling_Reduction_expectation_ratio
-- name    : PropVolSampling.Reduction.expectation_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:36.858993+00:00
-- url     : https://prove2.me/theorems/6885f947-dac4-4740-b5c8-9d8a62f68c30
-- title:
--   Proof of Theorem 1.3, p. 9 — expected objective under proportional volume sampling as a ratio of Cauchy–Binet sums
-- statement:
--   Let $d\ge 1$, $V=[v_1,\dots,v_n]$ a real $d\times n$ matrix, $\mu$ a probability measure on $\mathcal U_{\le k}$, and assume the normaliser $Z=\sum_S\mu(S)\det(V_SV_S^\top)$ is positive. Let $\mu'$ be proportional volume sampling with measure $\mu$. Then
--
--   1. $\displaystyle\sum_S\mu(S)\,E_{d-1}(V_SV_S^\top)=\sum_{|T|=d-1}\det(V_T^\top V_T)\Pr_\mu[\mathcal S\supseteq T]$;
--   2. $\displaystyle Z=\sum_{|R|=d}\det(V_R^\top V_R)\Pr_\mu[\mathcal S\supseteq R]$;
--   3. $$\mathbb E_{\mathcal S\sim\mu'}\Big[\operatorname{tr}\Big(\sum_{i\in\mathcal S}v_iv_i^\top\Big)^{-1}\Big]\le\frac{\sum_S\mu(S)\,E_{d-1}(V_SV_S^\top)}{Z}.$$
--
--   Together these bound the expected A-objective of the sampled set by $\sum_{|T|=d-1}\det(V_T^\top V_T)\Pr_\mu[\mathcal S\supseteq T]\big/\sum_{|R|=d}\det(V_R^\top V_R)\Pr_\mu[\mathcal S\supseteq R]$, the left-hand side of (7).
--
--   **Formalization Note** The page writes "$=$" in part 3. Equality fails when $\mu$ charges a set $S$ with $\operatorname{rank}V_S=d-1$: such $S$ has $\det(V_SV_S^\top)=0$, so it is never sampled, but $E_{d-1}(V_SV_S^\top)>0$ contributes to the right-hand side. The inequality is what the proof needs and is what is stated. Sets with singular $V_SV_S^\top$ have sampling probability $0$, so Lean's junk value $\operatorname{tr}(0)=0$ of their objective does not enter the expectation. $1\le d$ is added because $d-1$ is natural-number subtraction.
-- source:
--   Nikolov, Singh, Tantipongpipat, Proportional Volume Sampling and Approximation Algorithms for A-Optimal Design, arXiv:1802.08318v5, p. 9, proof of Theorem 1.3, first and second displays (first display printed with "="; stated with "≤")

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

namespace PropVolSampling.Reduction
open Matrix Finset

theorem expectation_ratio {d n : ℕ} (hd : 1 ≤ d) (V : Matrix (Fin d) (Fin n) ℝ) (k : ℕ)
    (μ : Finset (Fin n) → ℝ) (hμ : IsSetDist k μ) (hZ : 0 < pvsNormalizer V μ) :
    (∑ S, μ S * Ek (d - 1) (gram V S) =
        ∑ T ∈ powersetCard (d - 1) (univ : Finset (Fin n)),
          ((colSub V T)ᵀ * colSub V T).det * prSup μ T) ∧
      (pvsNormalizer V μ =
        ∑ R ∈ powersetCard d (univ : Finset (Fin n)),
          ((colSub V R)ᵀ * colSub V R).det * prSup μ R) ∧
      pvsExpect V μ (fun S => aObj (gram V S)) ≤
        (∑ S, μ S * Ek (d - 1) (gram V S)) / pvsNormalizer V μ := by sorry

end PropVolSampling.Reduction
