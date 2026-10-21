-- Prove2me | Theorems.Thm_PropVolSampling_Reduction_padding
-- name    : PropVolSampling.Reduction.padding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:38.854925+00:00
-- url     : https://prove2.me/theorems/0f096bf0-f3b1-4828-abdb-9fbc61149d67
-- title:
--   Proof of Theorem 1.3, p. 8 — adding vectors can only decrease $\operatorname{tr}(V_SV_S^\top)^{-1}$
-- statement:
--   Let $V=[v_1,\dots,v_n]$ be a real $d\times n$ matrix and $S\subseteq S'\subseteq[n]$ such that $V_SV_S^\top=\sum_{i\in S}v_iv_i^\top$ is positive definite. Then
--   $$\operatorname{tr}\Big(\sum_{i\in S'}v_iv_i^\top\Big)^{-1}\le\operatorname{tr}\Big(\sum_{i\in S}v_iv_i^\top\Big)^{-1}.$$
--
--   This is why step 4 of Algorithm 1, which pads a sampled set of size $|S|<k$ with $k-|S|$ arbitrary vectors, cannot hurt the guarantee.
--
--   **Formalization Note** Positive definiteness of the smaller Gram matrix is assumed; otherwise the page's objective is $+\infty$ and the claim is trivial, while Lean's inverse is the junk $0$.
-- source:
--   Nikolov, Singh, Tantipongpipat, Proportional Volume Sampling and Approximation Algorithms for A-Optimal Design, arXiv:1802.08318v5, p. 8, proof of Theorem 1.3, sentence after (5)

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

namespace PropVolSampling.Reduction
open Matrix Finset

theorem padding {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (S S' : Finset (Fin n)) (hSS' : S ⊆ S')
    (hpd : (gram V S).PosDef) :
    aObj (gram V S') ≤ aObj (gram V S) := by sorry

end PropVolSampling.Reduction
