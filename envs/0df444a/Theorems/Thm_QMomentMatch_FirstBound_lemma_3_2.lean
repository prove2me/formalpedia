-- Prove2me | Theorems.Thm_QMomentMatch_FirstBound_lemma_3_2
-- name    : QMomentMatch.FirstBound.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:59:04.080201+00:00
-- url     : https://prove2.me/theorems/0eaf467c-6123-4bd9-9115-373bbfb0d54d
-- title:
--   Lemma 3.2 — Taylor bound: $|q(z)-Q_r(z)|\le\frac{2}{(2r)!}\left(\frac{4d^2}{H}\right)^r z^r$ on $[0,H]$
-- statement:
--   Let $H\ge1$ and $d\ge0$ be integers with $d^2\le H/2$. Let $q(z)=\sum_{\ell=0}^d a_\ell z^\ell$ be a real polynomial of degree at most $d$ such that $|q(z)|\le1$ for every $z\in\{0,1,\dots,H\}$. For an integer $r\ge1$ let $Q_r(z)=\sum_{\ell=0}^{r-1}a_\ell z^\ell$ be the truncation of $q$ below degree $r$. Then for every real $z\in[0,H]$,
--   $$|q(z)-Q_r(z)|\le\frac{2}{(2r)!}\left(\frac{4d^2}{H}\right)^r z^r .$$
--
--   A polynomial bounded on an integer grid that is fine compared with its degree has small Taylor tail; this bound is applied to the univariate acceptance polynomial of Lemma 3.9.
--
--   Differences from the source:
--   - reading: $Q_r=\sum_{\ell=0}^{\min(r-1,r)}a_\ell z^\ell$ (printed) → $\sum_{\ell=0}^{r-1}$ (`Finset.range r` of the coefficients of $q$); reason: $\min(r-1,r)=r-1$; since $a_\ell=0$ for $\ell>d$ this equals the reading with $\min(r-1,d)$ too.
-- source:
--   Chandrima Kayal, Frédéric Magniez, Sayantan Sen, Dániel Szabó, STOC 2027 submission #564 (October 2026), Lemma 3.2, p. 16 (proof: Appendix A, pp. 42–43)

import Mathlib

namespace QMomentMatch.FirstBound

open Polynomial

/-- Lemma 3.2 (Taylor bound), p. 16 (proof: Appendix A, pp. 42–43). -/
theorem lemma_3_2 (H d r : ℕ) (hH : 1 ≤ H) (hd : (d : ℝ) ^ 2 ≤ (H : ℝ) / 2) (hr : 1 ≤ r)
    (q : ℝ[X]) (hq : q.natDegree ≤ d) (hbound : ∀ z : ℕ, z ≤ H → |q.eval (z : ℝ)| ≤ 1) :
    ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) H →
      |q.eval z - (∑ ℓ ∈ Finset.range r, C (q.coeff ℓ) * X ^ ℓ).eval z| ≤
        2 / ((2 * r).factorial : ℝ) * (4 * (d : ℝ) ^ 2 / H) ^ r * z ^ r := by sorry

end QMomentMatch.FirstBound
