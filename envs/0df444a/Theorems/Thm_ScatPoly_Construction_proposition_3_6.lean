-- Prove2me | Theorems.Thm_ScatPoly_Construction_proposition_3_6
-- name    : ScatPoly.Construction.proposition_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:56.820125+00:00
-- url     : https://prove2.me/theorems/673411e2-32e9-43b2-8daa-0f31bd7efe1f
-- title:
--   Proposition 3.6, p. 9 — for u ∈ ker L, v ∈ ker M nonzero: b ∈ ker T ⇔ bu ∈ ker M ⇔ bL(v) ∈ im M
-- statement:
--   Let $q = p^r$ be an odd prime power, $n = 2t$ with $t \ge 3$, $F = \mathbb F_{q^n}$, $h \in F$ with $h^{q^t+1} = -1$, and $L, M, T$ as in (3) and (8). For any nonzero vectors $u \in \ker L$, $v \in \ker M$ and any $b \in F$, the following statements are equivalent:
--
--   1. $b \in \ker T$;
--   2. $b\,u \in \ker M$;
--   3. $b\,L(v) \in \operatorname{im} M$.
--
--   This is the counterpart of Proposition 3.5 with the roles of $L$ and $M$ exchanged.
--
--   **Formalization Note.** Stated as the two biconditionals (1 ⇔ 2) and (2 ⇔ 3), with §3's standing hypotheses ($n = 2t$, $t \ge 3$, $q$ odd, $h^{q^t+1} = -1$).
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 9, Proposition 3.6

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

namespace ScatPoly.Construction

theorem proposition_3_6 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 3 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1)
    (u v b : F) (hu0 : u ≠ 0) (hu : Lmap q t h u = 0) (hv0 : v ≠ 0) (hv : Mmap q t h v = 0) :
    (Tmap q t h b = 0 ↔ Mmap q t h (b * u) = 0) ∧
    (Mmap q t h (b * u) = 0 ↔ b * Lmap q t h v ∈ Set.range (Mmap q t h)) := by sorry

end ScatPoly.Construction
