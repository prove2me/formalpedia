-- Prove2me | Theorems.Thm_PriceRobust_Stability_lam_nonneg_spectralRadius_lt_one
-- name    : PriceRobust.Stability.lam_nonneg_spectralRadius_lt_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:11.98312+00:00
-- url     : https://prove2.me/theorems/8ab915a9-02a5-45cd-b2a8-80af6746d3d9
-- title:
--   Proof of Theorem 3(a), p. 16 — Λ(R) ≥ 0 and its spectral radius is below 1
-- statement:
--   Consider the market of §3 with $a\ge 0$ and Assumptions (P), (Z), (IS), and let $\Lambda(R)=I-[T(R)]^{-1}R$. Then
--   $$\Lambda(R)\ge 0\quad\text{and}\quad \rho(\Lambda(R))<1,$$
--   where $\rho$ is the spectral radius over $\mathbb C$.
--
--   In block form $\Lambda(R)$ has zero diagonal firm blocks and off-diagonal blocks $-R^{-1}_{\mathcal N(i),\mathcal N(i)}R_{\mathcal N(i),\mathcal N(j)}$. The spectral bound is what makes the robust best-response map a contraction.
--
--   **Formalization Note** Nonnegativity is entrywise; the spectral radius is of $\Lambda(R)$ as a complex matrix.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), p. 16 (PDF 17), proof of Theorem 3(a)

import Mathlib
import Definitions.Def_PriceRobust_Stability_Model

open Matrix

namespace PriceRobust.Stability

theorem lam_nonneg_spectralRadius_lt_one {ι F : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]
    (M : Market ι F) (hM : M.Standing) :
    (∀ l m, 0 ≤ M.Lam l m) ∧ spectralRadius ℂ (M.Lam.map (algebraMap ℝ ℂ)) < 1 := by sorry

end PriceRobust.Stability
