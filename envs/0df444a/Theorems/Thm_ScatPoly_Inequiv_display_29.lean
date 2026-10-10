-- Prove2me | Theorems.Thm_ScatPoly_Inequiv_display_29
-- name    : ScatPoly.Inequiv.display_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:52.30004+00:00
-- url     : https://prove2.me/theorems/53b03af9-bf23-4c88-afb6-4b501359bc4b
-- title:
--   Display (29), p. 16 — U_h is GL(2, q^n)-equivalent to U_k iff h = ±k (t ≢ 2) or h = ℓk, ℓ^{q²+1} = 1 (t ≡ 2 mod 4)
-- statement:
--   Let $p$ be an odd prime, $r \ge 1$, $q = p^r$, $t > 4$, $n = 2t$, and $F = \mathbb F_{q^n}$. For $h \in F$ let $\psi_{h,t}(x) = x^q + x^{q^{t-1}} - h^{1-q^{t+1}} x^{q^{t+1}} + h^{1-q^{2t-1}} x^{q^{2t-1}}$ and $U_h = \{(x, \psi_{h,t}(x)) : x \in F\} \subseteq F^2$. Let $h, k \in F$ satisfy $h^{q^t+1} = k^{q^t+1} = -1$. Then $U_h$ is $\mathrm{GL}(2,q^n)$-equivalent to $U_k$ (some invertible $2\times 2$ matrix over $F$ maps $U_h$ onto $U_k$) if and only if
--   $$h = \begin{cases} \pm k, & t \not\equiv 2 \pmod 4,\\ \ell k \text{ for some } \ell \in F \text{ with } \ell^{q^2+1} = 1, & t \equiv 2 \pmod 4.\end{cases}$$
--
--   This is the classification on which Theorem 4.2 and the class-size count of Corollary 4.3 rest.
--
--   **Formalization Note.** "$U_h$ is GL-equivalent to $U_k$" is stated as `A.mulVec '' U_h = U_k` for some $A$ with invertible determinant; the page's "for each $x$ there exists $y$" (inclusion) is equivalent since both sets have $q^n$ elements and $A$ is injective. The case split is `t % 4 = 2` versus not. Note that $\psi_{-k,t} = \psi_{k,t}$, so $h = -k$ is a genuine case.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 16, proof of Theorem 4.2, display (29)

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

namespace ScatPoly.Inequiv

theorem display_29 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 4 < t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h k : F) (hh : h ∈ hSet F q t) (hk : k ∈ hSet F q t) :
    GLEquiv (ScatPoly.Construction.graph (ScatPoly.Construction.psi q t h)) (ScatPoly.Construction.graph (ScatPoly.Construction.psi q t k)) ↔
      if t % 4 = 2 then ∃ ℓ : F, ℓ ^ (q ^ 2 + 1) = 1 ∧ h = ℓ * k
      else h = k ∨ h = -k := by sorry

end ScatPoly.Inequiv
