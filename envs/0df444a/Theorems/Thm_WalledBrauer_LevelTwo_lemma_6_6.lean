-- Prove2me | Theorems.Thm_WalledBrauer_LevelTwo_lemma_6_6
-- name    : WalledBrauer.LevelTwo.lemma_6_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:50:03.930603+00:00
-- url     : https://prove2.me/theorems/6496abbd-e695-4aae-8ffe-2ce65a9bf7b3
-- title:
--   Lemma 6.6 (restated) — Jucys–Murphy images
-- statement:
--   Form $\Xi_1=0$ and recursively form $\Xi_{k+1}$ from the proposed crossing and contraction images by the Jucys–Murphy recursion (2.7), with the corrected source idempotent in the mixed case. Under Assumption 5.5 and the paper's parameter conditions, for every orientation $a$, position $k$, and allowed square-root family,
--   $$(\Xi_k-\beta_2^{a_k}f)1_a=-y_k f1_a.$$
--
--   This is the content of Lemma 6.6 before introducing the isomorphism $\Phi$ whose existence is the main goal. It identifies the polynomial generators in the image. **Formalization Note** The printed formula uses $\Phi$; the statement replaces $\Phi(\xi_k)$ with the recursive image $\Xi_k$, and uses zero-based indices.
-- source:
--   Sartori and Stroppel, Walled Brauer algebras as idempotent truncations of level 2 cyclotomic quotients, arXiv:1411.2771v2, p. 15, Lemma 6.6; p. 5, (2.7)

import Mathlib
import Definitions.Def_WalledBrauer_LevelTwo_Setting

namespace WalledBrauer.LevelTwo

/-- Lemma 6.6, p. 15, restated using the image recursion so the statement does
not assume the map whose existence is the goal. -/
theorem lemma_6_6 {r t m n : ℕ} {δ : ℤ}
    (hm : 0 < m) (hn : 0 < n)
    (h55 : Assumption55 r t m n δ)
    (R : Fin (r + t) → A r t m n δ) (hR : IsRootFamily δ R)
    (k : Fin (r + t)) (a : Orientation r t) :
    (xiImage δ R k.val -
      algebraMap ℂ (A r t m n δ) (βtwo m n δ (a.1 k)) * f δ) * cyclId δ a =
      -cyclY δ k * fAt δ a := by sorry

end WalledBrauer.LevelTwo
