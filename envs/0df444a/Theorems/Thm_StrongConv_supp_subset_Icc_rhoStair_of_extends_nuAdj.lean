-- Prove2me | Theorems.Thm_StrongConv_supp_subset_Icc_rhoStair_of_extends_nuAdj
-- name    : StrongConv.supp_subset_Icc_rhoStair_of_extends_nuAdj
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-04T22:55:04.140205+00:00
-- url     : https://prove2.me/theorems/70d47bfe-fdb1-4b86-a93d-85cef96f054d
-- title:
--   Corollary 8.6 — supp νₘ ⊆ [−ρₘ, ρₘ] for random regular graphs
-- statement:
--   Let $d \ge 2$ and $0 \le m \le d$. If $\mu$ is a compactly supported distribution (Definition 4.6) that agrees on real polynomials with the $m$-th coefficient $\nu_m$ of the expansion of $\mathbf E[\mathrm{tr}_N\, h(A^N)]$ in powers of $1/N$ (`nuAdj d m`), then $\operatorname{supp}\mu \subseteq [-\rho_m, \rho_m]$. Here $\rho_m = 2\sqrt{2d-1}$ if $2m - 1 \le \sqrt{2d-1}$ and $\rho_m = 2m - 1 + \frac{2d-1}{2m-1}$ otherwise. The paper's $\nu_m$ are the distributions of Theorem 7.1, the unique extensions (Lemma 4.7); the statement is phrased for every extension.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 26, Corollary 8.6

import Mathlib
import Definitions.Def_StrongConv

open Polynomial

namespace StrongConv

theorem supp_subset_Icc_rhoStair_of_extends_nuAdj (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (hm : m ≤ d)
    (μ : smoothFun →ₗ[ℝ] ℝ) (hμ : IsCSDistribution μ)
    (hext : ∀ h : ℝ[X], μ (polyFun h) = nuAdj d m h) :
    supp μ ⊆ Set.Icc (-rhoStair d m) (rhoStair d m) := by
  sorry

end StrongConv
