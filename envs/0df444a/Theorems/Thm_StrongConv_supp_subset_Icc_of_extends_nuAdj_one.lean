-- Prove2me | Theorems.Thm_StrongConv_supp_subset_Icc_of_extends_nuAdj_one
-- name    : StrongConv.supp_subset_Icc_of_extends_nuAdj_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-04T22:52:33.470853+00:00
-- url     : https://prove2.me/theorems/50f3368e-26d8-4c97-92ea-5ab7bd2a1a0e
-- title:
--   Corollary 8.4 — supp ν₁ ⊆ [−‖A_F‖, ‖A_F‖] for random regular graphs
-- statement:
--   For every $d$: if $\mu$ is a compactly supported distribution (Definition 4.6) that agrees on real polynomials with the first-order coefficient $\nu_1$ of the expansion of $\mathbf E[\mathrm{tr}_N\, h(A^N)]$ (`nuAdj d 1`), then $\operatorname{supp}\mu \subseteq [-\|A_{\rm F}\|, \|A_{\rm F}\|]$. The paper's $\nu_1$ is the distribution of Lemma 8.1. By Lemma 4.7 it is the unique compactly supported distribution extending the polynomial functional, so the statement is phrased for every such extension.
-- source:
--   Chen, C.-F., Garza-Vargas, J., Tropp, J. A. and van Handel, R., A new approach to strong convergence, Ann. of Math. (2) 203 (2026) 555–602, https://doi.org/10.4007/annals.2026.203.2.4 (arXiv:2405.16026v3, whose page numbers are used), p. 25, Corollary 8.4

import Mathlib
import Definitions.Def_StrongConv

open Polynomial

namespace StrongConv

theorem supp_subset_Icc_of_extends_nuAdj_one (d : ℕ) (μ : smoothFun →ₗ[ℝ] ℝ)
    (hμ : IsCSDistribution μ) (hext : ∀ h : ℝ[X], μ (polyFun h) = nuAdj d 1 h) :
    supp μ ⊆ Set.Icc (-‖adjFree d‖) ‖adjFree d‖ := by
  sorry

end StrongConv
