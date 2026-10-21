-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_breakpoint_separation
-- name    : RankOneBimatrix.BinSearch.breakpoint_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:04.583282+00:00
-- url     : https://prove2.me/theorems/5486041d-fdd5-4852-8d4c-a88db0dbd8a4
-- title:
--   Proof of Theorem 19, p. 22 — breakpoint separation
-- statement:
--   For rational input of combined binary length $L$, two distinct breakpoints are separated by at least an inverse power of two whose exponent is a polynomial in $L$. One polynomial applies to all dimensions and inputs.
--
--   $$\lambda\ne\lambda'\Longrightarrow |\lambda-\lambda'|\ge2^{-p(L)}.$$
--
--   This supplies the scale needed for a polynomial iteration bound. **Formalization Note** The input length includes $a$ as well as $A,b$.
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 22, proof of Theorem 19

import Definitions.Def_RankOneBimatrix_BinSearch_Setting

namespace RankOneBimatrix.BinSearch
open Matrix

/-- Proof of Theorem 19, p. 22: distinct rational-input breakpoints separate. -/
theorem breakpoint_separation :
    ∃ p : Polynomial ℕ,
      ∀ (m n : ℕ), 0 < m → 0 < n →
      ∀ (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ)
        (lam lam' : ℝ),
        IsBreakpoint (A.map (fun r => (r : ℝ))) (fun j => (b j : ℝ)) lam →
        IsBreakpoint (A.map (fun r => (r : ℝ))) (fun j => (b j : ℝ)) lam' →
        lam ≠ lam' →
        (1 : ℝ) / (2 : ℝ) ^ (p.eval (inputSize A a b)) ≤ |lam - lam'| := by sorry

end RankOneBimatrix.BinSearch
