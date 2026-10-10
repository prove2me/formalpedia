-- Prove2me | Theorems.Thm_ScatPoly_Inequiv_display_37
-- name    : ScatPoly.Inequiv.display_37
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:58.89921+00:00
-- url     : https://prove2.me/theorems/08ea5e8d-f8d9-4a1d-901c-61795647ecbf
-- title:
--   Display (37), pp. 20–21 — L_f, L_g PGL(2, q^n)-equivalent iff {f(x)/x} = {(cx+dg(x))/(ax+bg(x))} for an invertible matrix
-- statement:
--   Let $q = p^r$ with $p$ prime and $r \ge 1$, $n \ge 1$, $F = \mathbb F_{q^n}$, and let $f(x) = \sum_{i=0}^{n-1}\alpha_i x^{q^i}$ and $g(x) = \sum_{i=0}^{n-1}\beta_i x^{q^i}$ be two scattered polynomials over $F$ with $\alpha_0 = \beta_0 = 0$. Then the linear sets $L_f$ and $L_g$ are $\mathrm{PGL}(2,q^n)$-equivalent if and only if there is an invertible matrix $\begin{pmatrix} a & b\\ c & d\end{pmatrix}$ over $F$ such that $ax + bg(x) \ne 0$ for every $x \in \mathbb F_{q^n}^*$ and
--   $$\left\{\frac{f(x)}{x} : x \in \mathbb F_{q^n}^*\right\} = \left\{\frac{cx + dg(x)}{ax + bg(x)} : x \in \mathbb F_{q^n}^*\right\}.$$
--
--   This reduces the projective equivalence of linear sets to an equality of sets of field elements, on which the coefficient identities of Lemma 2.2 can act; it is the starting point of the proof of Theorem 5.1.
--
--   **Formalization Note.** The non-vanishing of $ax + bg(x)$ on $\mathbb F_{q^n}^*$ is made part of the condition (the page states it for $b = 1$ on p. 21): without it, Lean's convention $y/0 = 0$ would let a point $\langle(0, \cdot)\rangle$ pose as slope $0$. The matrix maps $L_g$ onto $L_f$, so the left-hand side is stated as the PGL-equivalence of $L_g$ to $L_f$ (the relation is symmetric). The hypotheses "scattered" and $\alpha_0 = \beta_0 = 0$ are kept as on the page; the equivalence does not need them. "Scattered" is the p. 2 definition, with $\mathbb F_q = \{c : c^q = c\}$.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, pp. 20–21, §5, display (37)

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

namespace ScatPoly.Inequiv

theorem display_37 (F : Type*) [Field F] [Fintype F] (p r n q : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 0 < r) (hq : q = p ^ r) (hn : 1 ≤ n) (hcard : Fintype.card F = q ^ n)
    (α β : ℕ → F) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hf : IsScatteredPoly q (ScatPoly.Construction.qpoly q n α)) (hg : IsScatteredPoly q (ScatPoly.Construction.qpoly q n β)) :
    PGLEquiv (linSet (ScatPoly.Construction.qpoly q n β)) (linSet (ScatPoly.Construction.qpoly q n α)) ↔
      ∃ a b c d : F, a * d - b * c ≠ 0 ∧
        (∀ x : F, x ≠ 0 → a * x + b * ScatPoly.Construction.qpoly q n β x ≠ 0) ∧
        {y : F | ∃ x : F, x ≠ 0 ∧ y = ScatPoly.Construction.qpoly q n α x / x} =
          {y : F | ∃ x : F, x ≠ 0 ∧
            y = (c * x + d * ScatPoly.Construction.qpoly q n β x) / (a * x + b * ScatPoly.Construction.qpoly q n β x)} := by sorry

end ScatPoly.Inequiv
