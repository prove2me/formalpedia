-- Prove2me | Theorems.Thm_ScatPoly_Construction_proposition_3_5
-- name    : ScatPoly.Construction.proposition_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:53.337143+00:00
-- url     : https://prove2.me/theorems/9e794738-3888-400c-9fa4-585bdeb749d8
-- title:
--   Proposition 3.5, p. 8 — for u ∈ ker L, v ∈ ker M nonzero: a ∈ ker R ⇔ av ∈ ker L ⇔ aM(u) ∈ im L
-- statement:
--   Let $q = p^r$ be an odd prime power, $n = 2t$ with $t \ge 3$, $F = \mathbb F_{q^n}$, $h \in F$ with $h^{q^t+1} = -1$, and $L, M, R$ as in (3) and (8). For any nonzero vectors $u \in \ker L$, $v \in \ker M$ and any $a \in F$, the following statements are equivalent:
--
--   1. $a \in \ker R$;
--   2. $av \in \ker L$;
--   3. $a\,M(u) \in \operatorname{im} L$.
--
--   **Formalization Note.** The equivalence is stated as the two biconditionals (1 ⇔ 2) and (2 ⇔ 3). The standing hypotheses of §3 ($n = 2t$, $t \ge 3$, $q$ odd, $h^{q^t+1} = -1$) are carried; the proof uses Proposition 3.3.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 8, Proposition 3.5

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

namespace ScatPoly.Construction

theorem proposition_3_5 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 3 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1)
    (u v a : F) (hu0 : u ≠ 0) (hu : Lmap q t h u = 0) (hv0 : v ≠ 0) (hv : Mmap q t h v = 0) :
    (Rmap q t h a = 0 ↔ Lmap q t h (a * v) = 0) ∧
    (Lmap q t h (a * v) = 0 ↔ a * Mmap q t h u ∈ Set.range (Lmap q t h)) := by sorry

end ScatPoly.Construction
