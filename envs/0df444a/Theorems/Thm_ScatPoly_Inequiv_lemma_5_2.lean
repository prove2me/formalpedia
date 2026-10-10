-- Prove2me | Theorems.Thm_ScatPoly_Inequiv_lemma_5_2
-- name    : ScatPoly.Inequiv.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:13.525065+00:00
-- url     : https://prove2.me/theorems/cbc9db01-913f-4f2a-8c12-ed1087b62d80
-- title:
--   Lemma 5.2, p. 21 — if (38) holds for f = ψ_{h,t}, g = ψ_{k,t}, t > 4, then (h/k)^{q²+1} = 1 and U_h ~_ΓL U_k
-- statement:
--   Let $p$ be an odd prime, $r \ge 1$, $q = p^r$, $t > 4$, $n = 2t$, $F = \mathbb F_{q^n}$, and let $h, k \in F$ satisfy $h^{q^t+1} = k^{q^t+1} = -1$. Write $f = \psi_{h,t} = \sum_{i=1}^{n-1}\alpha_i x^{q^i}$ and $g = \psi_{k,t} = \sum_{i=1}^{n-1}\beta_i x^{q^i}$. If there exists $d \in F$ such that
--   $$\left\{\sum_{i=1}^{n-1}\alpha_i x^{q^i-1} : x \in \mathbb F_{q^n}^*\right\} = \left\{d\sum_{i=1}^{n-1}\beta_i x^{q^i-1} : x \in \mathbb F_{q^n}^*\right\} \tag{38}$$
--   then $(h/k)^{q^2+1} = 1$, and $U_h = \{(x,\psi_{h,t}(x))\}$ is $\Gamma\mathrm L(2,q^n)$-equivalent to $U_k$.
--
--   This settles the case $b = 0$ of (37) in the proof of Theorem 5.1.
--
--   **Formalization Note.** For $x \ne 0$, $\sum_{i=1}^{n-1}\alpha_i x^{q^i-1} = \psi_{h,t}(x)/x$ because $\alpha_0 = 0$; (38) is stated in this quotient form.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 21, Lemma 5.2 with display (38)

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

namespace ScatPoly.Inequiv

theorem lemma_5_2 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 4 < t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h k : F) (hh : h ∈ hSet F q t) (hk : k ∈ hSet F q t) (d : F)
    (h38 : {y : F | ∃ x : F, x ≠ 0 ∧ y = ScatPoly.Construction.psi q t h x / x} =
      {y : F | ∃ x : F, x ≠ 0 ∧ y = d * (ScatPoly.Construction.psi q t k x / x)}) :
    (h / k) ^ (q ^ 2 + 1) = 1 ∧ GammaLEquiv (ScatPoly.Construction.graph (ScatPoly.Construction.psi q t h)) (ScatPoly.Construction.graph (ScatPoly.Construction.psi q t k)) := by sorry

end ScatPoly.Inequiv
