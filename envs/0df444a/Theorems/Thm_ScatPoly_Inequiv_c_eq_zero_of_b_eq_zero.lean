-- Prove2me | Theorems.Thm_ScatPoly_Inequiv_c_eq_zero_of_b_eq_zero
-- name    : ScatPoly.Inequiv.c_eq_zero_of_b_eq_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:09:58.805196+00:00
-- url     : https://prove2.me/theorems/66269527-b894-4e6c-9eb5-6fab6697422a
-- title:
--   §5, p. 21 — case b = 0 of (37): α_0 = β_0 = 0 forces c = 0 ([7, Lemma 3.6])
-- statement:
--   Let $q = p^r$ with $p$ prime and $r \ge 1$, $n \ge 1$, $F = \mathbb F_{q^n}$, and let $f(x) = \sum_{i=0}^{n-1}\alpha_i x^{q^i}$ and $g(x) = \sum_{i=0}^{n-1}\beta_i x^{q^i}$ be scattered polynomials over $F$ with $\alpha_0 = \beta_0 = 0$. If $c, d \in F$ satisfy
--   $$\left\{\sum_{i=0}^{n-1}\alpha_i x^{q^i-1} : x \in \mathbb F_{q^n}^*\right\} = \left\{c + d\sum_{i=0}^{n-1}\beta_i x^{q^i-1} : x \in \mathbb F_{q^n}^*\right\},$$
--   then $c = 0$.
--
--   This is the form (37) takes when $b = 0$ and $a = 1$; the page derives $c = 0$ "by Lemma 3.6 in [7]", which turns (37) into (38), the hypothesis of Lemma 5.2.
--
--   **Formalization Note.** [7]'s own hypotheses are not printed; the statement asserts exactly what the page asserts in this setting, with the page's hypotheses. $q^i - 1$ is a natural-number exponent, exact since $q \ge 1$.
-- source:
--   Longobardi, Marino, Trombetti & Zhou, A large family of maximum scattered linear sets of PG(1, q^n) and their associated MRD codes, arXiv:2102.08287v3, p. 21, §5, case b = 0 (by [7, Lemma 3.6])

import Mathlib
import Definitions.Def_ScatPoly_Inequiv_Model

namespace ScatPoly.Inequiv

theorem c_eq_zero_of_b_eq_zero (F : Type*) [Field F] [Fintype F] (p r n q : ℕ) [Fact p.Prime] [CharP F p]
    (hr : 0 < r) (hq : q = p ^ r) (hn : 1 ≤ n) (hcard : Fintype.card F = q ^ n)
    (α β : ℕ → F) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hf : IsScatteredPoly q (ScatPoly.Construction.qpoly q n α)) (hg : IsScatteredPoly q (ScatPoly.Construction.qpoly q n β))
    (c d : F)
    (hset : {y : F | ∃ x : F, x ≠ 0 ∧ y = ∑ i ∈ Finset.range n, α i * x ^ (q ^ i - 1)} =
      {y : F | ∃ x : F, x ≠ 0 ∧ y = c + d * ∑ i ∈ Finset.range n, β i * x ^ (q ^ i - 1)}) :
    c = 0 := by sorry

end ScatPoly.Inequiv
