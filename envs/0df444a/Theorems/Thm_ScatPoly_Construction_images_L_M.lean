-- Prove2me | Theorems.Thm_ScatPoly_Construction_images_L_M
-- name    : ScatPoly.Construction.images_L_M
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:17:15.453295+00:00
-- url     : https://prove2.me/theorems/c15709b7-e683-467a-bb21-5477769211a0
-- title:
--   §3, p. 7, displays (6)–(7) — im L and im M, 1-dimensional 𝔽_{q^t}-subspaces
-- statement:
--   Let $q = p^r$ be an odd prime power, $t \ge 3$, $F = \mathbb F_{q^{2t}}$, $\mathbb F_{q^t} \subseteq F$ the subfield of order $q^t$, $h \in F$ with $h^{q^t+1} = -1$, and $L, M$ as in display (3). Then
--   $$\operatorname{im} L = \{z \in F : z^{q^t} + h^{q^t-q} z = 0\}, \tag{6}$$
--   $$\operatorname{im} M = \{z \in F : z^{q^t} - h^{q^t-q^{t-1}} z = 0\}, \tag{7}$$
--   and both are 1-dimensional $\mathbb F_{q^t}$-subspaces of $F$ (closed under addition and $\mathbb F_{q^t}$-scalars, containing $0$, of cardinality $q^t$).
--
--   These images are the summands of the second decomposition $F = \operatorname{im} L \oplus \operatorname{im} M$ (Proposition 3.3) and are used to test membership in Propositions 3.5 and 3.6.
--
--   **Formalization Note.** As for (4)–(5), "1-dimensional subspace" is `IsFqSubspace` plus `HasRank … 1`; $h^{q^t-q}$ is `h ^ q ^ t / h ^ q` and $h^{q^t-q^{t-1}}$ is `h ^ q ^ t / h ^ q ^ (t-1)`.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 7, §3, displays (6)–(7) and the sentence after (7)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

namespace ScatPoly.Construction

open ScatCaps.LinearSets in
theorem images_L_M (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 3 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1) :
    Set.range (Lmap q t h) = {z : F | z ^ q ^ t + h ^ q ^ t / h ^ q * z = 0} ∧
    Set.range (Mmap q t h) = {z : F | z ^ q ^ t - h ^ q ^ t / h ^ q ^ (t - 1) * z = 0} ∧
    IsFqSubspace (subfieldOf F p r t) (Set.range (Lmap q t h)) ∧
    HasRank (subfieldOf F p r t) (Set.range (Lmap q t h)) 1 ∧
    IsFqSubspace (subfieldOf F p r t) (Set.range (Mmap q t h)) ∧
    HasRank (subfieldOf F p r t) (Set.range (Mmap q t h)) 1 := by sorry

end ScatPoly.Construction
