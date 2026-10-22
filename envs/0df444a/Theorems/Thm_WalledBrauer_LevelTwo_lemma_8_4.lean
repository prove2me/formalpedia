-- Prove2me | Theorems.Thm_WalledBrauer_LevelTwo_lemma_8_4
-- name    : WalledBrauer.LevelTwo.lemma_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:15.082902+00:00
-- url     : https://prove2.me/theorems/a66629cb-af88-49d4-9f9c-723001c56a42
-- title:
--   Lemma 8.4 — the contraction parameter is −δ
-- statement:
--   Let $\tau_k$ be the image of the ordinary contraction generator under (6.4). For every permitted family of polynomial square roots of the $b_jf$, under Assumption 5.5 and the paper's positive integer parameter conditions,
--   $$\tau_k^2=-\delta\tau_k.$$
--
--   This is relation (Br5) for the proposed isomorphism, and changes the loop parameter from $\omega_0=m+n$ to $-\delta$. **Formalization Note** The assertion concerns the global sum over orientations and all adjacent positions; each square-root choice is quantified universally.
-- source:
--   Sartori and Stroppel, Walled Brauer algebras as idempotent truncations of level 2 cyclotomic quotients, arXiv:1411.2771v2, p. 18, Lemma 8.4

import Mathlib
import Definitions.Def_WalledBrauer_LevelTwo_Setting

namespace WalledBrauer.LevelTwo

/-- Lemma 8.4, p. 18. The truncation changes the loop parameter to `-δ`. -/
theorem lemma_8_4 {r t m n : ℕ} {δ : ℤ}
    (hm : 0 < m) (hn : 0 < n)
    (h55 : Assumption55 r t m n δ)
    (R : Fin (r + t) → A r t m n δ) (hR : IsRootFamily δ R)
    (k : Fin (r + t)) (hk : k.val + 1 < r + t) :
    totalTau δ R k hk * totalTau δ R k hk =
      -(δ : ℂ) • totalTau δ R k hk := by sorry

end WalledBrauer.LevelTwo
