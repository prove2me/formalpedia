-- Prove2me | Theorems.Thm_PriceRobust_Stability_lemma_B1_g
-- name    : PriceRobust.Stability.lemma_B1_g
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:10.492884+00:00
-- url     : https://prove2.me/theorems/1152da6c-8cb0-4e46-87bc-cd403c963e12
-- title:
--   Lemma B.1(g), Appendix p. 7 — if I − Q is a ZP-matrix with Q ≥ 0, then ρ(Q) < 1
-- statement:
--   Let $Q$ be a real square matrix with $Q\ge 0$ entrywise. If $A=I-Q$ is a ZP-matrix, then
--   $$\rho(Q)<1,$$
--   where $\rho(Q)$ is the spectral radius of $Q$, the largest modulus of its (complex) eigenvalues.
--
--   **Formalization Note** The spectral radius is that of $Q$ viewed as a complex matrix, `spectralRadius ℂ`, so complex eigenvalues are counted; it takes values in $[0,\infty]$.
-- source:
--   Federgruen & Hu, Global robust stability in a general price and assortment competition model, submitted manuscript (TSpace / SSRN 3010503), Online Appendix p. 7 (PDF 27), Lemma B.1(g)

import Mathlib
import Definitions.Def_PriceRobust_Stability_ZPMatrix

open Matrix

namespace PriceRobust.Stability

theorem lemma_B1_g {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (hQ : ∀ l m, 0 ≤ Q l m) (hA : IsZPMatrix (1 - Q)) :
    spectralRadius ℂ (Q.map (algebraMap ℝ ℂ)) < 1 := by sorry

end PriceRobust.Stability
