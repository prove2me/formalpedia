-- Prove2me | Theorems.Thm_ScatPoly_Construction_scattered_iff
-- name    : ScatPoly.Construction.scattered_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:41.000711+00:00
-- url     : https://prove2.me/theorems/144239ff-dd64-4391-bd60-b12e3d09799f
-- title:
--   §1, p. 2 — L_f is scattered iff f is a scattered polynomial iff (f(γx) = γf(x), x ≠ 0 ⇒ γ ∈ 𝔽_q)
-- statement:
--   Let $q = p^r$ with $p$ prime and $r \ge 1$, let $F = \mathbb F_{q^n}$ be the finite field of order $q^n$, and let $\mathbb F_q \subseteq F$ be its subfield of order $q$. Let
--   $$f(x) = \sum_{i=0}^{n-1} c_i\, x^{q^i}, \qquad c_i \in F,$$
--   be any $q$-polynomial, $U_f = \{(x, f(x)) : x \in F\} \subseteq F^2$, and $L_f$ the $\mathbb F_q$-linear set of $\mathrm{PG}(1, q^n)$ defined by $U_f$. Then the following are equivalent:
--
--   1. $L_f$ is scattered, i.e. every point $\langle u \rangle_{\mathbb F_{q^n}}$, $u \in U_f \setminus \{0\}$, has weight one: whenever $u \in U_f\setminus\{0\}$, $c \in F$ and $cu \in U_f$, then $c \in \mathbb F_q$;
--   2. $f$ is a scattered polynomial: for all $z, y \in F^*$, $f(z)/z = f(y)/y$ implies $z = cy$ for some $c \in \mathbb F_q$;
--   3. for all $x, \gamma \in F$ with $x \neq 0$,
--   $$f(\gamma x) = \gamma f(x) \quad\Longrightarrow\quad \gamma \in \mathbb F_q.$$
--
--   This is the observation of the introduction that turns the geometric notion (a scattered linear set of the projective line) into the algebraic one (a scattered polynomial), and gives the form (3) in which the main theorem is proved.
--
--   **Formalization Note.** The paper defines a scattered linear set of rank $k$ by $|L_U| = (q^k-1)/(q-1)$; item 1 uses the equivalent, standard weight-one form, which is the published definition `ScatCaps.LinearSets.IsScattered` (with $K = F$, all scalars of $F$ allowed). That equivalence is not part of this claim. $\mathbb F_q$ is the fixed field of $x \mapsto x^q$ (`subfieldOf F p r 1`); for $|F| = q^n$ it is the unique subfield of order $q$.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 2, §1 (the paragraph defining scattered polynomials)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

namespace ScatPoly.Construction

open ScatCaps.LinearSets in
theorem scattered_iff (F : Type*) [Field F] [Fintype F] (p r n q : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 0 < r) (hq : q = p ^ r) (hcard : Fintype.card F = q ^ n) (c : ℕ → F) :
    (IsScattered (subfieldOf F p r 1) ⊤ (graph (qpoly q n c)) ↔
        IsScatteredPoly (subfieldOf F p r 1) (qpoly q n c)) ∧
    (IsScatteredPoly (subfieldOf F p r 1) (qpoly q n c) ↔
        ∀ x γ : F, x ≠ 0 → qpoly q n c (γ * x) = γ * qpoly q n c x →
          γ ∈ subfieldOf F p r 1) := by sorry

end ScatPoly.Construction
