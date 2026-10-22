-- Prove2me | Theorems.Thm_WalledBrauer_LevelTwo_lemma_8_7
-- name    : WalledBrauer.LevelTwo.lemma_8_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:02.608342+00:00
-- url     : https://prove2.me/theorems/be7d9bd5-e599-4ad4-b224-64c443e0e4bd
-- title:
--   Lemma 8.7 — the inverse sandwich identity
-- statement:
--   In the cyclotomic algebra $A$, let $f_{k-1}$ be the truncation through position $k-1$, and let $b_k$ be the element of (6.1). Under Assumption 5.5 and the paper's positive integer parameter conditions, for each orientation $a$ and adjacent position $k$,
--   $$e_k\,b_k^{-1}\,e_k f_{k-1}1_a=e_k f_{k-1}1_a.$$
--
--   This identity is the parameter-change calculation used in the contraction relation. **Formalization Note** The inverse is the inverse of $b_k f_{k-1}$ in the $f_{k-1}$ corner, including at the first position where $f_0=1$. Lean uses zero-based positions.
-- source:
--   Sartori and Stroppel, Walled Brauer algebras as idempotent truncations of level 2 cyclotomic quotients, arXiv:1411.2771v2, p. 20, Lemma 8.7, (8.16)

import Mathlib
import Definitions.Def_WalledBrauer_LevelTwo_Setting

namespace WalledBrauer.LevelTwo

/-- Lemma 8.7, p. 20. The inverse is taken in the `f_{k-1}` corner. -/
theorem lemma_8_7 {r t m n : ℕ} {δ : ℤ}
    (hm : 0 < m) (hn : 0 < n)
    (h55 : Assumption55 r t m n δ)
    (k : Fin (r + t)) (hk : k.val + 1 < r + t) (a : Orientation r t) :
    let e : A r t m n δ := cyclTotal δ .e k
    let bk : A r t m n δ := b δ k
    let fk : A r t m n δ := fGlobalPrefix δ k.val
    let fa : A r t m n δ := fPrefix δ a k.val
    e * cornerInverse δ bk fk * e * fa = e * fa := by sorry

end WalledBrauer.LevelTwo
