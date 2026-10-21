-- Prove2me | Theorems.Thm_PropVolSampling_Reduction_cp_le_opt
-- name    : PropVolSampling.Reduction.cp_le_opt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:36.917547+00:00
-- url     : https://prove2.me/theorems/3366d531-3b74-447a-acde-ed2d07b7d45b
-- title:
--   §2, p. 7 — $\mathrm{CP}\le\mathrm{OPT}$
-- statement:
--   Let $V=[v_1,\dots,v_n]$ be a real $d\times n$ matrix and let $x$ be an optimal solution of the relaxation
--   $$\min\ \operatorname{tr}\Big(\sum_{i=1}^nx_iv_iv_i^\top\Big)^{-1}\quad\text{s.t.}\quad\sum_{i=1}^nx_i=k,\quad 0\le x_i\le1,$$
--   with finite value $\mathrm{CP}$. Then for every $S\subseteq[n]$ with $|S|=k$ and $V_SV_S^\top$ positive definite,
--   $$\operatorname{tr}\Big(\sum_{i=1}^nx_iv_iv_i^\top\Big)^{-1}\le\operatorname{tr}\big(V_SV_S^\top\big)^{-1}.$$
--   In particular $\mathrm{CP}\le\mathrm{OPT}$.
--
--   The relaxation is a lower bound for the A-optimal design problem; it is the benchmark against which Theorem 1.3 measures the sampled set.
--
--   **Formalization Note** $\mathrm{OPT}$ is the minimum of $\operatorname{tr}(V_SV_S^\top)^{-1}$ over $k$-sets, with value $+\infty$ on sets with singular $V_SV_S^\top$; the statement quantifies over the $k$-sets with positive definite Gram matrix instead of taking an infimum, which avoids Lean's junk value of the inverse.
-- source:
--   Nikolov, Singh, Tantipongpipat, Proportional Volume Sampling and Approximation Algorithms for A-Optimal Design, arXiv:1802.08318v5, p. 7, §2, "CP ≤ OPT" (after (1)–(3))

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

namespace PropVolSampling.Reduction
open Matrix Finset

theorem cp_le_opt {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (k : ℕ) (x : Fin n → ℝ)
    (hx : IsRelaxOptimal V k x) (S : Finset (Fin n)) (hS : S.card = k) (hpd : (gram V S).PosDef) :
    aObj (weightedGram V x) ≤ aObj (gram V S) := by sorry

end PropVolSampling.Reduction
