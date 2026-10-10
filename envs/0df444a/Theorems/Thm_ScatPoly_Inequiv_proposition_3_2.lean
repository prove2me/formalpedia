-- Prove2me | Theorems.Thm_ScatPoly_Inequiv_proposition_3_2
-- name    : ScatPoly.Inequiv.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:50.68142+00:00
-- url     : https://prove2.me/theorems/d598c307-a452-408b-9a3e-70e8d44b85b6
-- title:
--   Proposition 3.2, p. 7 — h^{q^t+1} = −1 implies h^{q²+1} ≠ 1 and h^{q^{t−2}} ≠ −h
-- statement:
--   Let $p$ be an odd prime, $r \ge 1$, $q = p^r$, $t \ge 1$, and let $F = \mathbb F_{q^{2t}}$ be the finite field of order $q^{2t}$ (characteristic $p$). If $h \in F$ satisfies $h^{q^t+1} = -1$, then
--   $$h^{q^2+1} \neq 1 \qquad\text{and}\qquad h^{q^{t-2}} \neq -h.$$
--
--   Both inequalities are used in the classification of the $\mathrm{GL}(2,q^n)$-equivalences between the sets $U_h$ (proof of Theorem 4.2) and in Case (iii) of the proof of Lemma 5.3.
--
--   **Formalization Note.** The page states $t \ge 1$ but $h^{q^{t-2}}$ is undefined at $t = 1$; the exponent is read as $q^{3t-2}$, which gives the same element for $t \ge 2$ because $h^{q^{2t}} = h$, and is defined at $t = 1$. The hypothesis "$q$ odd", which the page's proof uses ("as $q$ is odd") but the statement omits, is added; for $q$ even and $h = 1$ the claim fails. This is the same statement, with the same Lean shape, as `ScatPoly.Construction.proposition_3_2` of the companion mission.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 7, Proposition 3.2

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

namespace ScatPoly.Inequiv

theorem proposition_3_2 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 1 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hh : h ^ (q ^ t + 1) = -1) :
    h ^ (q ^ 2 + 1) ≠ 1 ∧ h ^ q ^ (3 * t - 2) ≠ -h := by sorry

end ScatPoly.Inequiv
