-- Prove2me | Theorems.Thm_PropVolSampling_Reduction_inequality_5
-- name    : PropVolSampling.Reduction.inequality_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:36.182157+00:00
-- url     : https://prove2.me/theorems/c528f541-c656-4355-8b7e-a8a9523346a1
-- title:
--   Inequality (5), p. 8 — $\mathbb E_{\mathcal S\sim\mu'}[\operatorname{tr}(\sum_{i\in\mathcal S}v_iv_i^\top)^{-1}]\le\alpha\operatorname{tr}(\sum_i x_iv_iv_i^\top)^{-1}$
-- statement:
--   Let $1\le d\le k\le n$ be integers and $V=[v_1,\dots,v_n]$ a real $d\times n$ matrix. Let $x\in[0,1]^n$ with $\sum_ix_i=k$ be such that $\sum_ix_iv_iv_i^\top$ is positive definite, and let $\mu$ be a probability measure on $\mathcal U_{\le k}$ that is $\alpha$-approximate $(d-1,d)$-wise independent with respect to $x$, with positive normaliser $Z=\sum_S\mu(S)\det(V_SV_S^\top)$. If $\mu'$ is proportional volume sampling with measure $\mu$, then
--   $$\mathbb E_{\mathcal S\sim\mu'}\Big[\operatorname{tr}\Big(\sum_{i\in\mathcal S}v_iv_i^\top\Big)^{-1}\Big]\le\alpha\,\operatorname{tr}\Big(\sum_{i\in[n]}x_iv_iv_i^\top\Big)^{-1}.$$
--
--   Applied to an optimal solution $x$ of the relaxation (1)–(3), the right-hand side is $\alpha\,\mathrm{CP}\le\alpha\,\mathrm{OPT}$; this is the core of Theorem 1.3.
--
--   **Formalization Note** Approximate independence is in the cross-multiplied form of Definition 1.2. Positivity of $Z$ is assumed so that $\mu'$ is a probability distribution, and positive definiteness of $\sum_ix_iv_iv_i^\top$ so that the right-hand side is the page's finite value rather than Lean's junk $\operatorname{tr}(0)$. $1\le d$ is added because $d-1$ is natural-number subtraction.
-- source:
--   Nikolov, Singh, Tantipongpipat, Proportional Volume Sampling and Approximation Algorithms for A-Optimal Design, arXiv:1802.08318v5, p. 8, inequality (5) (proved on pp. 9–10 via (7)–(9))

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

namespace PropVolSampling.Reduction
open Matrix Finset

theorem inequality_5 {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (k : ℕ) (hd : 1 ≤ d) (hdk : d ≤ k)
    (hkn : k ≤ n) (x : Fin n → ℝ) (hx : IsRelaxFeasible k x) (hpd : (weightedGram V x).PosDef)
    (μ : Finset (Fin n) → ℝ) (hμ : IsSetDist k μ) (α : ℝ) (hα : IsApproxIndep d α x μ)
    (hZ : 0 < pvsNormalizer V μ) :
    pvsExpect V μ (fun S => aObj (gram V S)) ≤ α * aObj (weightedGram V x) := by sorry

end PropVolSampling.Reduction
