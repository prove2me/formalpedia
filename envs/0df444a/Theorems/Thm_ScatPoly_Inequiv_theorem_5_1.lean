-- Prove2me | Theorems.Thm_ScatPoly_Inequiv_theorem_5_1
-- name    : ScatPoly.Inequiv.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:10:11.558093+00:00
-- url     : https://prove2.me/theorems/87b07cd6-1d23-40b4-a8ec-9f4b7c662c6b
-- title:
--   Theorem 5.1, p. 20 — for q = p^r odd and t > 4 there are ≥ ⌊(q^t+1)/(8rt)⌋ (resp. ⌊(q^t+1)/(4rt(q²+1))⌋) PΓL-inequivalent L_{h,t}
-- statement:
--   Let $p$ be an odd prime, let $r, t$ be positive integers with $t > 4$, $q = p^r$, $n = 2t$, and $F = \mathbb F_{q^n}$. For $h \in H = \{h \in F : h^{q^t+1} = -1\}$ let
--   $$L_{h,t} = \{\langle (x, \psi_{h,t}(x))\rangle_{\mathbb F_{q^n}} : x \in \mathbb F_{q^n}^*\}, \qquad \psi_{h,t}(x) = x^q + x^{q^{t-1}} - h^{1-q^{t+1}} x^{q^{t+1}} + h^{1-q^{2t-1}} x^{q^{2t-1}}.$$
--   The total number $M$ of $\mathrm{P\Gamma L}(2,q^n)$-inequivalent linear sets $L_{h,t}$, $h \in H$, satisfies
--   $$M \ge \begin{cases} \left\lfloor \dfrac{q^t+1}{8rt} \right\rfloor, & t \not\equiv 2 \pmod 4,\\[2ex] \left\lfloor \dfrac{q^t+1}{4rt(q^2+1)} \right\rfloor, & t \equiv 2 \pmod 4.\end{cases}$$
--   Equivalently: there is a set $S \subseteq H$ of at least that many elements such that $L_{h,t}$ and $L_{k,t}$ are not $\mathrm{P\Gamma L}(2,q^n)$-equivalent for distinct $h, k \in S$.
--
--   For $h \notin \mathbb F_{q^t}$ the sets $L_{h,t}$ are maximum scattered (Theorem 3.1); the bound grows exponentially in $n$, while for the previously known families of maximum scattered linear sets of $\mathrm{PG}(1,q^n)$ the number of classes is at most Euler's $\varphi(n)$ times a function of $q$ (Table 1, p. 3).
--
--   **Formalization Note.** "$M \ge B$" is stated as the existence of $B$ elements of $H$ whose linear sets are pairwise inequivalent; since $\mathrm{P\Gamma L}$-equivalence is an equivalence relation, this is the same as saying the sets $L_{h,t}$, $h \in H$, meet at least $B$ classes. $\lfloor\cdot\rfloor$ is natural-number division, whose denominator is positive under $r \ge 1$, $t > 4$. "Maximum scattered" is descriptive and not a hypothesis; $H$ is not restricted to $h \notin \mathbb F_{q^t}$, matching the count $|H| = q^t + 1$ on p. 26. Equivalence is taken on the point sets $L_{h,t}$ themselves (not on slope sets), via the collineations $P \mapsto \{A v^\sigma : v \in P\}$ with $A$ invertible and $\sigma \in \mathrm{Aut}(F)$.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 20, Theorem 5.1 with display (36)

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

namespace ScatPoly.Inequiv

theorem theorem_5_1 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 4 < t)
    (hcard : Fintype.card F = q ^ (2 * t)) :
    ∃ S : Finset F, (∀ h ∈ S, h ∈ hSet F q t) ∧
      (if t % 4 = 2 then (q ^ t + 1) / (4 * r * t * (q ^ 2 + 1))
        else (q ^ t + 1) / (8 * r * t)) ≤ S.card ∧
      ∀ h ∈ S, ∀ k ∈ S, h ≠ k →
        ¬ PGammaLEquiv (linSet (ScatPoly.Construction.psi q t h)) (linSet (ScatPoly.Construction.psi q t k)) := by sorry

end ScatPoly.Inequiv
