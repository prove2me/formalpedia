-- Prove2me | Theorems.Thm_ScatPoly_Construction_proposition_3_2
-- name    : ScatPoly.Construction.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:41.366958+00:00
-- url     : https://prove2.me/theorems/5fc5db05-7029-4af6-9f4f-b6bd93d7de5c
-- title:
--   Proposition 3.2, p. 7 — h^{q^t+1} = −1 implies h^{q²+1} ≠ 1 and h^{q^{t−2}} ≠ −h (q odd)
-- statement:
--   Let $q = p^r$ with $p$ an odd prime and $r \ge 1$, let $t \ge 1$, and let $F = \mathbb F_{q^{2t}}$. If $h \in F$ satisfies $h^{q^t+1} = -1$, then
--   $$h^{q^2+1} \neq 1 \qquad\text{and}\qquad h^{q^{3t-2}} \neq -h .$$
--   Since $h^{q^{2t}} = h$ for every $h \in F$, the second conclusion is the paper's $h^{q^{t-2}} \neq -h$ whenever $t \ge 2$.
--
--   This proposition is what rules out common elements of $\ker L$ and $\ker M$ (Proposition 3.3) and elements of $\ker R$ in $\mathbb F_{q^t}$ (Lemma 3.4).
--
--   **Formalization Note.** The hypothesis "$q$ odd" is not printed in the statement but is used by the proof ("as $q$ is odd") and is needed: for $q$ even, $h = 1$ satisfies $h^{q^t+1} = 1 = -1$ but not the first conclusion. The paper allows $t \ge 1$, where $h^{q^{t-2}}$ is undefined at $t = 1$; the exponent is therefore read as $q^{3t-2}$, which agrees with $q^{t-2}$ on $F$ for $t \ge 2$ (natural-number subtraction $3t-2$ is exact for $t \ge 1$).
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 7, Proposition 3.2

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

namespace ScatPoly.Construction

theorem proposition_3_2 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 1 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1) :
    h ^ (q ^ 2 + 1) ≠ 1 ∧ h ^ q ^ (3 * t - 2) ≠ -h := by sorry

end ScatPoly.Construction
