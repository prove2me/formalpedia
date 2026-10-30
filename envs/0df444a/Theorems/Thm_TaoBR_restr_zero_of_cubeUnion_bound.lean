-- Prove2me | Theorems.Thm_TaoBR_restr_zero_of_cubeUnion_bound
-- name    : TaoBR.restr_zero_of_cubeUnion_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T17:07:36.955838+00:00
-- url     : https://prove2.me/theorems/1b4b7ad0-d7e5-44fd-a518-b3b4aaee9fed
-- title:
--   p. 7 — the reduction of Theorem 1.2 to the bound (4) on unions of c-cubes
-- statement:
--   Let $n \ge 2$, $1 < p < 2$, $1 < q_0 \le p$ and $0 < c < 1$. Suppose there is $C$ such that every finite union $E$ of $c$-cubes $k + [-c/2, c/2]^n$, $k \in \mathbf Z^n$, satisfies
--   $$\|\Re\chi_E\|_{L^p(S^{n-1})} \le C|E|^{1/q_0}.$$
--   Then $R(q, 0)$ holds for every $1 \le q < q_0$.
--
--   *Formalization note.* The page passes through the Lorentz-space estimate (3), $\|\Re f\|_p \lesssim \|f\|_{q_0,1}$; the statement combines the page's reductions into one implication from the bound (4) to $R(q, 0)$, so it needs no Lorentz spaces. It drops the page's standing assumption $R(p, \alpha)$, which these reductions do not use, and takes the exponent $q_0$ free in $(1, p]$; on the page, $1/q_0 = 1/p + C/\log(1/\alpha)$ with $\alpha$ small, which gives $1 < q_0 < p$. The paper's $c \sim 1$, "chosen so that $\hat\chi$ is positive on the unit sphere", is read as $0 < c < 1$, a range on which the transform of the indicator of a $c$-cube does not vanish on the unit sphere. The $c$-cubes are the translates of the cube of side $c$ to the points of $\mathbf Z^n$, as in the page's convolution of a measure on $\mathbf Z^n$ with that cube.
-- source:
--   Tao, T., The Bochner–Riesz conjecture implies the restriction conjecture, Duke Math. J. 96 (1999) 363–375, https://doi.org/10.1215/S0012-7094-99-09610-2 (the author's preprint, https://www.math.ucla.edu/~tao/preprints/restriction.dvi, whose page numbers are used), p. 7, the reduction to (4)

import Mathlib
import Definitions.Def_TaoBR

open MeasureTheory
open scoped ENNReal

namespace TaoBR

theorem restr_zero_of_cubeUnion_bound (n : ℕ) (hn : 2 ≤ n) (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (q₀ : ℝ) (hq₀ : 1 < q₀) (hq₀p : q₀ ≤ p) (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (h : ∃ C : ℝ, ∀ S : Set (E n), IsCubeUnion c S →
      eLpNorm (restriction (S.indicator fun _ => (1 : ℂ))) (ENNReal.ofReal p) (sphereMeasure n) ≤
        ENNReal.ofReal (C * (volume S).toReal ^ (1 / q₀))) :
    ∀ q : ℝ≥0∞, 1 ≤ q → q < ENNReal.ofReal q₀ → Restr n q 0 := by
  sorry

end TaoBR
