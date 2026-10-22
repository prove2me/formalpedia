-- Prove2me | Theorems.Thm_WalledBrauer_LevelTwo_lemma_8_5
-- name    : WalledBrauer.LevelTwo.lemma_8_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:56.638371+00:00
-- url     : https://prove2.me/theorems/13808935-1075-4a7b-9b5e-6e05e13f2b2c
-- title:
--   Lemma 8.5 — involution on equal orientations
-- statement:
--   Let $a$ be an orientation with equal arrows at adjacent positions $k,k+1$, and let $\sigma_k$ be the global crossing image of (6.3). Under Assumption 5.5 and the paper's parameter conditions, for every allowed square-root family,
--   $$\sigma_k^2 1_a=f1_a.$$
--
--   This verifies the equal-orientation case of relation (Br3) in the corner algebra. **Formalization Note** Lean's adjacent positions are zero-based; $f1_a$ is the spectral truncation defined in the setting.
-- source:
--   Sartori and Stroppel, Walled Brauer algebras as idempotent truncations of level 2 cyclotomic quotients, arXiv:1411.2771v2, pp. 18–19, Lemma 8.5

import Mathlib
import Definitions.Def_WalledBrauer_LevelTwo_Setting

namespace WalledBrauer.LevelTwo

/-- Lemma 8.5, p. 18, in the same-orientation component. -/
theorem lemma_8_5 {r t m n : ℕ} {δ : ℤ}
    (hm : 0 < m) (hn : 0 < n)
    (h55 : Assumption55 r t m n δ)
    (R : Fin (r + t) → A r t m n δ) (hR : IsRootFamily δ R)
    (k : Fin (r + t)) (hk : k.val + 1 < r + t) (a : Orientation r t)
    (ha : adjacent a k) :
    totalSigma δ R k hk * totalSigma δ R k hk * cyclId δ a = fAt δ a := by sorry

end WalledBrauer.LevelTwo
