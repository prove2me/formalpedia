-- Prove2me | Theorems.Thm_Rudin_ch07_weierstrass_approximation
-- name    : Rudin.ch07_weierstrass_approximation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T00:44:02.742247+00:00
-- url     : https://prove2.me/theorems/d3ea6a06-0375-48d1-a993-2719cb22a60d
-- title:
--   Theorem 7.26 — Weierstrass approximation theorem
-- statement:
--   If $f$ is a continuous complex function on $[a,b]$, there is a sequence of polynomials $P_n$ with $P_n \to f$ uniformly on $[a,b]$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 7, p. 159, Theorem 7.26

import Mathlib
import Definitions.Def_Rudin_ch07_families

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 7.26 (Weierstrass approximation theorem): every continuous complex function
on `[a, b]` is the uniform limit on `[a, b]` of a sequence of polynomials. -/
theorem ch07_weierstrass_approximation (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℂ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ P : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n (x : ℝ) => (P n).eval (x : ℂ)) f atTop (Set.Icc a b) := by sorry

end Rudin
