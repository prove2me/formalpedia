-- Prove2me | Theorems.Thm_ScatPoly_Construction_theorem_3_1
-- name    : ScatPoly.Construction.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T19:16:50.078306+00:00
-- url     : https://prove2.me/theorems/5997b6c0-a6c9-4e77-b886-412f70db82a4
-- title:
--   Theorem 3.1, p. 6 — for q odd, n = 2t, t ≥ 3, h ∉ 𝔽_{q^t}, h^{q^t+1} = −1, ψ_{h,t} is scattered
-- statement:
--   Let $n = 2t$ with $t \ge 3$, and let $q = p^r$ be an odd prime power ($p$ an odd prime, $r \ge 1$). Let $F = \mathbb F_{q^n}$, and let $\mathbb F_q \subseteq \mathbb F_{q^t} \subseteq F$ be its subfields of orders $q$ and $q^t$. For each $h \in \mathbb F_{q^n} \setminus \mathbb F_{q^t}$ such that $h^{q^t+1} = -1$, the $\mathbb F_q$-linearized polynomial
--   $$\psi_{h,t}(x) = x^q + x^{q^{t-1}} - h^{1-q^{t+1}} x^{q^{t+1}} + h^{1-q^{2t-1}} x^{q^{2t-1}} \in \mathbb F_{q^n}[x] \tag{2}$$
--   is scattered: for all $z, y \in F^*$,
--   $$\frac{\psi_{h,t}(z)}{z} = \frac{\psi_{h,t}(y)}{y} \quad\Longrightarrow\quad z = c\,y \text{ for some } c \in \mathbb F_q .$$
--
--   Consequently the linear set $L_{\psi_{h,t}} = \{\langle (x, \psi_{h,t}(x)) \rangle_{\mathbb F_{q^n}} : x \in F^*\}$ is a maximum scattered $\mathbb F_q$-linear set of $\mathrm{PG}(1, q^n)$ (§1, p. 2), and $\psi_{h,t}$ yields an MRD code. For $t = 3$ these are the scattered polynomials of Bartoli, Zanella and Zullo (p. 6).
--
--   **Formalization Note.** $F$ is a finite field of characteristic $p$ with $|F| = q^{2t}$; $\mathbb F_q$ and $\mathbb F_{q^t}$ are the fixed fields of $x \mapsto x^q$ and $x \mapsto x^{q^t}$ (published `subfieldOf F p r 1` and `subfieldOf F p r t`), the unique subfields of those orders. "Scattered" is the definition of p. 2, with $z, y$ ranging over all of $F^*$. Negative powers of $h$ are field quotients, exact because $h^{q^t+1} = -1$ forces $h \neq 0$. The hypothesis $h \notin \mathbb F_{q^t}$ is kept as printed: for $h \in \mathbb F_{q^t}$ one has $h \in \mathbb F_{q^2}$ and $\psi_{h,t}$ reduces to already known polynomials.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 6, Theorem 3.1, display (2)

import Mathlib
import Definitions.Def_ScatCaps_LinearSets_Model
import Definitions.Def_ScatPoly_Construction_Model

namespace ScatPoly.Construction

open ScatCaps.LinearSets in
theorem theorem_3_1 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 3 ≤ t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h : F) (hht : h ∉ subfieldOf F p r t) (hh : h ^ (q ^ t + 1) = -1) :
    IsScatteredPoly (subfieldOf F p r 1) (psi q t h) := by sorry

end ScatPoly.Construction
