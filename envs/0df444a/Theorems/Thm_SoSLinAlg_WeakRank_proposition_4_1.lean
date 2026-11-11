-- Prove2me | Theorems.Thm_SoSLinAlg_WeakRank_proposition_4_1
-- name    : SoSLinAlg.WeakRank.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:31:40.033912+00:00
-- url     : https://prove2.me/theorems/707bb73d-70f3-4354-a118-6dcdef6529c0
-- title:
--   Proposition 4.1 — the top component vanishes on Z_d
-- statement:
--   Let $n>r\ge1$ and $0\le d\le r$ be integers, and let $X,Y$ be $n\times r$ matrices of real indeterminates. Let $Z_d$ be the real locus $XY^\top=0$, $\operatorname{rank}X+\operatorname{rank}Y\le d$.
--
--   If $f\in\mathbb R[X,Y]$ has degree at most $2d$ and admits polynomials $h_{ij}$ of degrees at most $2r-2$ with
--   $$f=\sum_{i,j=1}^n h_{ij}\bigl((XY^\top)_{ij}-\delta_{ij}\bigr),$$
--   then its homogeneous component of degree $2d$ satisfies
--   $$\forall (X,Y)\in Z_d,\qquad f^{[2d]}(X,Y)=0.$$
--   Here $\delta_{ij}$ is the Kronecker delta and the homogeneous component collects the monomials of exactly the indicated total degree.
--
--   The statement controls the highest allowed component of a low-degree combination of the identity-rank equations. It includes both endpoints $d=0$ and $d=r$, with no homogeneity assumption on $f$ itself.
--
--   Differences from the source:
--   - encoding: matrix entries indexed by [n] and [r] → entries indexed by Fin n and Fin r, and equations by pairs of indices; reason: zero-based finite indices enumerate precisely the same entries and equations
--   - encoding: the zero polynomial has degree minus infinity → totalDegree 0 = 0 at nonnegative upper bounds; reason: all bounds in this item are nonnegative, so the allowed polynomials are unchanged
--   - encoding: Z_d is introduced for positive d but the propositions allow d = 0 → Z is defined for every natural d, including Z_0; reason: the source explicitly uses Z_0 = {(0,0)} in its proof, PDF p.18
-- source:
--   Dmitriy Kunisky, Xifan Yu, The sum-of-squares complexity of linear-algebraic principles, STOC 2027 submission #1181 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1181.pdf, Proposition 4.1, PDF p.14 (printed p.12)

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_Z

namespace SoSLinAlg.WeakRank

/-- Proposition 4.1, PDF p.14 (printed p.12). Both d = 0 and d = r are included.
Since r ≥ 1, the natural bound 2*r - 2 is the source's integer bound. -/
theorem proposition_4_1 {n r d : ℕ} (hr : 0 < r) (hrn : r < n) (hdr : d ≤ r)
    (f : Poly n r) (hf : f.totalDegree ≤ 2 * d)
    (h : (Fin n × Fin n) → Poly n r)
    (hdeg : ∀ ij, (h ij).totalDegree ≤ 2 * r - 2)
    (hrep : f = ∑ ij, h ij * WRank r (1 : Matrix (Fin n) (Fin n) ℝ) ij) :
    VanishesOnZ d (MvPolynomial.homogeneousComponent (2 * d) f) := by sorry

end SoSLinAlg.WeakRank
