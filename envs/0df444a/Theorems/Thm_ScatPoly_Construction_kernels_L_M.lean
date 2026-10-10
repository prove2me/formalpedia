-- Prove2me | Theorems.Thm_ScatPoly_Construction_kernels_L_M
-- name    : ScatPoly.Construction.kernels_L_M
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:58.242222+00:00
-- url     : https://prove2.me/theorems/c24c9f7a-22d1-4d74-a945-17697d87afb7
-- title:
--   §3, p. 7, displays (4)–(5) — ker L and ker M, 1-dimensional 𝔽_{q^t}-subspaces
-- statement:
--   Let $q = p^r$ be an odd prime power, $t \ge 3$, $F = \mathbb F_{q^{2t}}$, $\mathbb F_{q^t} \subseteq F$ the subfield of order $q^t$, $h \in F$ with $h^{q^t+1} = -1$, and $L, M$ as in display (3). Then
--   $$\ker L = \{x \in F : x - h^{q^{2t-1}-q^t} x^{q^t} = 0\}, \tag{4}$$
--   $$\ker M = \{x \in F : x + h^{q^{t+1}-q^t} x^{q^t} = 0\}, \tag{5}$$
--   and both are 1-dimensional $\mathbb F_{q^t}$-subspaces of $F$: each contains $0$, is closed under addition and under multiplication by elements of $\mathbb F_{q^t}$, and has exactly $|\mathbb F_{q^t}| = q^t$ elements.
--
--   These kernels are the two summands of the first direct-sum decomposition $F = \ker L \oplus \ker M$ (Proposition 3.3).
--
--   **Formalization Note.** "1-dimensional $\mathbb F_{q^t}$-subspace" is expressed with the published definitions `IsFqSubspace` (contains 0, closed under $+$ and under $\mathbb F_{q^t}$-scalars) and `HasRank … 1` (cardinality $|\mathbb F_{q^t}|^1$). Negative or difference powers of $h$ are written as quotients, e.g. $h^{q^{2t-1}-q^t}$ as `h ^ q ^ (2*t-1) / h ^ q ^ t`, exact since $h \neq 0$.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 7, §3, displays (4)–(5) and the sentence after (7)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

namespace ScatPoly.Construction

open ScatCaps.LinearSets in
theorem kernels_L_M (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 3 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1) :
    (∀ x : F, Lmap q t h x = 0 ↔ x - h ^ q ^ (2 * t - 1) / h ^ q ^ t * x ^ q ^ t = 0) ∧
    (∀ x : F, Mmap q t h x = 0 ↔ x + h ^ q ^ (t + 1) / h ^ q ^ t * x ^ q ^ t = 0) ∧
    IsFqSubspace (subfieldOf F p r t) {x : F | Lmap q t h x = 0} ∧
    HasRank (subfieldOf F p r t) {x : F | Lmap q t h x = 0} 1 ∧
    IsFqSubspace (subfieldOf F p r t) {x : F | Mmap q t h x = 0} ∧
    HasRank (subfieldOf F p r t) {x : F | Mmap q t h x = 0} 1 := by sorry

end ScatPoly.Construction
