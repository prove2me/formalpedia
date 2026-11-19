-- Prove2me | Theorems.Thm_PPSLattice_Supplement_theorem_6_23
-- name    : PPSLattice.Supplement.theorem_6_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T09:02:58.614893+00:00
-- url     : https://prove2.me/theorems/4c84dab2-68d1-4355-bf75-6e601d3ab845
-- title:
--   Theorem 6.23 — batched IBE gives bounded-set robust PPS
-- statement:
--   A selectively secure batched IBE scheme makes Construction 6.22 robustly payload hiding for every queried set of size at most the batch bound $B$, retaining set-key queries both before and after the challenge.
--
--   Differences from the source:
--   - encoding: The source leaves the identity family and oracle transcript implicit → Lean supplies the family as a predicate containing $[2^\lambda]$ and makes every pre- and post-challenge target-exclusion and cardinality check explicit; reason: this is the literal selective-security game of Definition 6.21.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Theorem 6.23, p.57

import Mathlib
import Definitions.Def_PPSLattice_Supplement_BIBE
set_option autoImplicit false

namespace PPSLattice.Supplement

/-- **Theorem 6.23**, Goyal--Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f...),
p.57. Selective security of batched IBE implies robust payload hiding of Construction 6.22 for
key sets of cardinality at most the setup batch bound `B`.

**Formalization Note.** The BIBE game and the resulting RPPS game retain key queries both before
and after the challenge. The identity space contains `[2^λ]`. -/
theorem theorem_6_23 (E : BIBE) (Identity : ℕ → Set ℕ) (B : ℕ)
    (hB : 1 ≤ B) (hE : E.IsScheme Identity) :
    (construction622 B E).RobustPayloadHidingUpTo B := by sorry

end PPSLattice.Supplement
