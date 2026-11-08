-- Prove2me | Theorems.Thm_SpikyCVP_eq_3_3
-- name    : SpikyCVP.eq_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:49:58.840507+00:00
-- url     : https://prove2.me/theorems/12891cb0-21d6-4747-9609-01e8092ff8ea
-- title:
--   Equation (3.3) — the super-Gaussian is a Gaussian scale mixture
-- statement:
--   Let $1\le p<2$, $r>0$ and $x\in\mathbb R^n$. Then
--
--   $$f_p(x,r)=\exp\Big(-\frac{\|x\|_p^p}{r^p}\Big)=\int_{\mathbb R^n_{>0}}\rho(x,s)\,h_p(s,r)\,ds,$$
--
--   where $\rho(x,s)=\exp(-\pi\sum_j x_j^2/s_j^2)$ and $h_p(s,r)=\prod_j g_{p/2}(\pi r^2/s_j^2)\,2\pi r^2/s_j^3$.
--
--   Equivalently, the posterior $P_{x,r}=\rho(x,\cdot)h_p(\cdot,r)/f_p(x,r)$ is a probability density. The identity is used in Lemma 4.4 to compute the overlap of two posteriors in closed form.
--
--   Differences from the source: none.
-- source:
--   Aggarwal, Morolia, How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector Problem, STOC 2027 submission (manuscript sha256 535c3bcc…), Equation (3.3), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_SpikyCVP_post

open MeasureTheory

namespace SpikyCVP

/-- **Equation (3.3): the super-Gaussian is a Gaussian scale mixture.**
Aggarwal, Morolia, *How to Round Spiky Balls into Submission; And Faster Algorithms For The Closest Vector
Problem*, STOC 2027 submission (manuscript sha256 535c3bcc…), Equation (3.3), p.17 (PDF p.19).

For `1 ≤ p < 2` (§3), `r > 0` and `x ∈ ℝⁿ`,
`fp(x, r) = ∫_{R^n_{>0}} ρ(x, s) hp(s, r) ds`.

**Formalization Note.** The left side is positive, so the identity cannot hold through a junk value of the
integral. It says that the posterior density `Px,r` of (3.4) integrates to `1`. -/
theorem eq_3_3 {n : ℕ} (p r : ℝ) (hp1 : 1 ≤ p) (hp2 : p < 2) (hr : 0 < r) (x : Fin n → ℝ) :
    fp p x r = ∫ s in orthant n, rho x s * prior p r s := by sorry

end SpikyCVP
