-- Prove2me | Theorems.Thm_WalledBrauer_LevelTwo_corner_dimension
-- name    : WalledBrauer.LevelTwo.corner_dimension
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:07.823052+00:00
-- url     : https://prove2.me/theorems/8cca10e6-3b2b-4934-acf6-4661bb5fbe19
-- title:
--   Corollary 5.8 and Lemma 5.9 (restated) — corner dimension
-- statement:
--   Fix an orientation $a$. For positive $m,n$ with $m,n\ge r+t$ satisfying Assumption 5.5, the corresponding oriented corner of the spectral truncation has dimension
--   $$\dim_{\mathbb C}(f1_a\,A\,f1_a)=(r+t)!.$$
--
--   This is the numerical consequence of Corollary 5.8 and Lemma 5.9 used in the injectivity argument. **Formalization Note** The source states the comparison through category $\mathcal O$; the mission states only its dimension consequence in the algebraic model. The dimension is the finrank of the corner submodule, with no assumed finite-dimensionality instance.
-- source:
--   Sartori and Stroppel, Walled Brauer algebras as idempotent truncations of level 2 cyclotomic quotients, arXiv:1411.2771v2, p. 12, Corollary 5.8 and Lemma 5.9; p. 15, proof of Theorem 6.2

import Mathlib
import Definitions.Def_WalledBrauer_LevelTwo_Setting

namespace WalledBrauer.LevelTwo

/-- The dimension content of Corollary 5.8 and Lemma 5.9, p. 12. -/
theorem corner_dimension {r t m n : ℕ} {δ : ℤ}
    (hm : 0 < m) (hn : 0 < n) (hmn : r + t ≤ m ∧ r + t ≤ n)
    (h55 : Assumption55 r t m n δ) (a : Orientation r t) :
    Module.finrank ℂ (@cornerSubmodule r t m n δ (@fAt r t m n δ a)) =
      Nat.factorial (r + t) := by sorry

end WalledBrauer.LevelTwo
