-- Prove2me | Theorems.Thm_SysRiskPortfolio_CoER_landsman_step
-- name    : SysRiskPortfolio.CoER.landsman_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:49:43.356747+00:00
-- url     : https://prove2.me/theorems/48add33c-214e-4ffc-b4bf-51d906c30b70
-- title:
--   (A.7)–(A.8), p. 29 — optimizer of transformed objective
-- statement:
--   Let $n=m+1\ge2$, let $\widehat\Sigma$ be positive definite, and define $\Delta,Q,w^*$ by the paper's partition and printed formula. If $\lambda>\sqrt{\Delta^\top Q^{-1}\Delta}$, then $w^*$ sums to one and uniquely maximizes
--   $$w\longmapsto w^\top\widehat\mu-\lambda\sqrt{w^\top\widehat\Sigma w}\quad\text{over }\{w:\mathbf1^\top w=1\}.$$
--   This isolates the deterministic optimization result invoked in the proof of Proposition 2.
--
--   **Formalization Note** The statement allows arbitrary transformed data with positive definite $\widehat\Sigma$; the paper applies it to the transformed Gaussian portfolio data of (A.6).
-- source:
--   Capponi & Rubtsov, Systemic Risk Driven Portfolio Selection, SSRN working paper 3394471 (version of May 25, 2019), p. 29, (A.7)–(A.8)

import Mathlib
import Definitions.Def_SysRiskPortfolio_CoER_Optimizer

namespace SysRiskPortfolio.CoER

open Matrix

theorem landsman_step {m : ℕ} (hm : 1 ≤ m) (d : OptimData m) (hS : d.SigHat.PosDef) (hlam : Real.sqrt (Del d ⬝ᵥ ((Qm d)⁻¹ *ᵥ Del d)) < d.lam) : (∑ i, wStar d i) = 1 ∧ (∀ w : Fin (m + 1) → ℝ, (∑ i, w i) = 1 → objective d w ≤ objective d (wStar d)) ∧ (∀ w : Fin (m + 1) → ℝ, (∑ i, w i) = 1 → objective d w = objective d (wStar d) → w = wStar d) := by sorry

end SysRiskPortfolio.CoER
