-- Prove2me | Theorems.Thm_ScatPoly_Inequiv_card_H
-- name    : ScatPoly.Inequiv.card_H
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:54.679711+00:00
-- url     : https://prove2.me/theorems/20070b2e-750d-4d80-94eb-5095b9fea4b3
-- title:
--   §5, p. 26 — |{h ∈ 𝔽_{q^n} : h^{q^t+1} = −1}| = q^t + 1
-- statement:
--   Let $p$ be an odd prime, $r \ge 1$, $q = p^r$, $t \ge 1$, and let $F = \mathbb F_{q^{2t}}$. Then the set $H = \{h \in F : h^{q^t+1} = -1\}$ has exactly $q^t + 1$ elements:
--   $$\bigl|\{h \in \mathbb F_{q^{2t}} : h^{q^t+1} = -1\}\bigr| = q^t + 1.$$
--
--   $H$ indexes the family $L_{h,t}$; its size is the numerator of the lower bound in Theorem 5.1, whose proof divides it by the sizes of the equivalence classes.
--
--   **Formalization Note.** The cardinality is `Nat.card` of the subtype of $F$ cut out by $h^{q^t+1} = -1$.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 26, §5, proof of Theorem 5.1

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

namespace ScatPoly.Inequiv

theorem card_H (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 1 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t)) :
    Nat.card (hSet F q t) = q ^ t + 1 := by sorry

end ScatPoly.Inequiv
