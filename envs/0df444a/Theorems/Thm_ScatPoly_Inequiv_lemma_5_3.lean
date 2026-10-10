-- Prove2me | Theorems.Thm_ScatPoly_Inequiv_lemma_5_3
-- name    : ScatPoly.Inequiv.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:56.067896+00:00
-- url     : https://prove2.me/theorems/70c62f4a-abbd-4ade-8bb5-2ba5a9c47d1d
-- title:
--   Lemma 5.3, p. 22 — under (41): t even ⇒ a = 0; t odd, a ≠ 0 ⇒ f = g; a = 0 ⇒ γ_0 = d = 0
-- statement:
--   Let $p$ be an odd prime, $r \ge 1$, $q = p^r$, $t > 4$, $n = 2t$, $F = \mathbb F_{q^n}$, $h, k \in F$ with $h^{q^t+1} = k^{q^t+1} = -1$, $f = \psi_{h,t} = \sum_{i=1}^{n-1}\alpha_i x^{q^i}$ and $g = \psi_{k,t}$. This is the setting of p. 21, case $b = 1$ of (37): let $a, c, d \in F$ with $\bar c = c - da \ne 0$, and let $\bar g(y) = \sum_{i=0}^{n-1}\gamma_i y^{q^i}$ be the inverse of the map $x \mapsto ax + g(x)$, i.e.
--   $$\bar g\bigl(ax + g(x)\bigr) = x \quad\text{for all } x \in \mathbb F_{q^n}, \tag{47}$$
--   with $d + \bar c\gamma_0 = 0$ (40). Suppose (41) holds:
--   $$\left\{\frac{1}{\bar c}\sum_{i=1}^{n-1}\alpha_i x^{q^i-1} : x \in \mathbb F_{q^n}^*\right\} = \left\{\sum_{i=1}^{n-1}\gamma_i x^{q^i-1} : x \in \mathbb F_{q^n}^*\right\}. \tag{41}$$
--   Then
--
--   1. if $t$ is even, $a = 0$;
--   2. if $t$ is odd and $a \ne 0$, then $f = g$;
--   3. in particular, when $a = 0$, $\gamma_0 = d = 0$.
--
--   Together with Lemma 5.2 this shows that every PGL-equivalence between two sets $L_{h,t}$, $L_{k,t}$ comes from a $\Gamma\mathrm L$-equivalence of $U_h$, $U_k$ or from the case $a = d = 0$, which drives the count of Theorem 5.1.
--
--   **Formalization Note.** "(41) holds" is read in the setting in which the page states it (p. 21): $b = 1$, $\bar c \ne 0$, (47) and (40) are hypotheses. That $ax + g(x) = 0$ has no nonzero solution follows from (47). $\sum_{i\ge1}\alpha_i x^{q^i-1}$ is written $\psi_{h,t}(x)/x$ (equal for $x \ne 0$ since $\alpha_0 = 0$), and the right side of (41) is the literal sum over $i = 1, \dots, n-1$. "$f = g$" is equality of $\psi_{h,t}$ and $\psi_{k,t}$ as maps $F \to F$, which is equality as $q$-polynomials of $q$-degree $< n$.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 22, Lemma 5.3, in the setting of p. 21 (b = 1, c̄ = c − da, ḡ) with displays (40), (41), (47)

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

namespace ScatPoly.Inequiv

theorem lemma_5_3 (F : Type*) [Field F] [Fintype F] (p r t q : ℕ) [Fact p.Prime] [CharP F p]
    (hp : Odd p) (hr : 0 < r) (hq : q = p ^ r) (ht : 4 < t)
    (hcard : Fintype.card F = q ^ (2 * t))
    (h k : F) (hh : h ∈ hSet F q t) (hk : k ∈ hSet F q t) (a c d : F) (γ : ℕ → F)
    (hcbar : c - d * a ≠ 0)
    (h47 : ∀ x : F, ScatPoly.Construction.qpoly q (2 * t) γ (a * x + ScatPoly.Construction.psi q t k x) = x)
    (h40 : d + (c - d * a) * γ 0 = 0)
    (h41 : {y : F | ∃ x : F, x ≠ 0 ∧ y = 1 / (c - d * a) * (ScatPoly.Construction.psi q t h x / x)} =
      {y : F | ∃ x : F, x ≠ 0 ∧ y = ∑ i ∈ Finset.Ico 1 (2 * t), γ i * x ^ (q ^ i - 1)}) :
    (Even t → a = 0) ∧
    (Odd t → a ≠ 0 → ScatPoly.Construction.psi q t h = ScatPoly.Construction.psi q t k) ∧
    (a = 0 → γ 0 = 0 ∧ d = 0) := by sorry

end ScatPoly.Inequiv
