-- Prove2me | Theorems.Thm_ScatPoly_Construction_proposition_3_3
-- name    : ScatPoly.Construction.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:11.811633+00:00
-- url     : https://prove2.me/theorems/4c305bce-9015-48ba-8316-09ff56470e0f
-- title:
--   Proposition 3.3, p. 7 — 𝔽_{q^n} = ker L ⊕ ker M = im L ⊕ im M
-- statement:
--   Let $q = p^r$ be an odd prime power, $n = 2t$ with $t \ge 3$, $F = \mathbb F_{q^n}$, $h \in F$ with $h^{q^t+1} = -1$, and $L, M$ as in display (3). Then $F$, seen as an $\mathbb F_{q^t}$-vector space, is the direct sum of $\ker L$ and $\ker M$, and also of $\operatorname{im} L$ and $\operatorname{im} M$:
--   $$F = \ker L \oplus \ker M = \operatorname{im} L \oplus \operatorname{im} M .$$
--   Concretely, every $x \in F$ can be written in exactly one way as $x = a + b$ with $L(a) = 0$ and $M(b) = 0$, and in exactly one way as $x = a' + b'$ with $a' \in \operatorname{im} L$ and $b' \in \operatorname{im} M$.
--
--   The decomposition $\psi_{h,t} = L + M$ along these two splittings is the frame in which the main theorem is proved.
--
--   **Formalization Note.** The direct sum is stated as unique decomposition (`∃!` on pairs). That the four summands are $\mathbb F_{q^t}$-subspaces is the content of the items for displays (4)–(7). The standing hypotheses $q$ odd and $h^{q^t+1} = -1$ of §3 are carried, since the proof uses Proposition 3.2.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 7, Proposition 3.3

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

namespace ScatPoly.Construction

theorem proposition_3_3 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 3 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1) :
    (∀ x : F, ∃! ab : F × F, Lmap q t h ab.1 = 0 ∧ Mmap q t h ab.2 = 0 ∧ ab.1 + ab.2 = x) ∧
    (∀ x : F, ∃! ab : F × F,
      ab.1 ∈ Set.range (Lmap q t h) ∧ ab.2 ∈ Set.range (Mmap q t h) ∧ ab.1 + ab.2 = x) := by sorry

end ScatPoly.Construction
