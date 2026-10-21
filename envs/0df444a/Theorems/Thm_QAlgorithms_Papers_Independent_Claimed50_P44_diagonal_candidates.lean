-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P44_diagonal_candidates
-- name    : QAlgorithms.Papers.Independent.Claimed50.P44.diagonal_candidates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T11:10:17.862429+00:00
-- url     : https://prove2.me/theorems/b62dbdb1-cdb4-4c48-963f-3d31d3e7b14d
-- title:
--   Necessary diagonal stationary and boundary equations
-- statement:
--   For a physical standard-form resource with parameters $a,b,c_1,c_2$, and diagonal physical pure-input covariance $D=\operatorname{diag}(d_1,d_2)$ or formal $D=0$, put $\alpha(x)=2d_1+a+2c_1x+bx^2$ and $\beta(y)=2d_2+a-2c_2y+by^2$. Both are strictly positive for every real argument. For $f(x,y)=|1-xy|+\sqrt{\alpha(x)\beta(y)}$, away from $xy=1$ vanishing of both partial derivatives is equivalent to
--
--   $$x=\sigma\sqrt{\alpha(x)/\beta(y)}(by-c_2),\qquad y=\sigma\sqrt{\beta(y)/\alpha(x)}(bx+c_1),$$
--
--   where $\sigma=1$ when $1-xy>0$ and $\sigma=-1$ otherwise. At such a stationary point, if $L=x(b^2-1)+bc_1\ne0$, then $y=c_2(bx+c_1)/L$ and $c_2^2\alpha(x)=L^2\beta(c_2(bx+c_1)/L)$.
--
--   On the boundary $xy=1$, write $y=1/x$ with $x\ne0$. The derivative of $\alpha(x)\beta(1/x)$ equals $2P(x)/x^3$, where
--
--   $$P(x)=b(2d_2+a)x^4+[c_1(2d_2+a)-bc_2]x^3+[(2d_1+a)c_2-bc_1]x-b(2d_1+a).$$
--
--   Boundary stationarity is therefore equivalent to $P(x)=0$. These are candidate conditions, not a complete isolated-root search: $L$ may vanish, $P$ may be identically zero, and squared equations require the original sign conditions.
-- source:
--   Improving fidelity of continuous-variable teleportation via local operations, arXiv:quant-ph/0202102v3, PDF p. 5, §III, Eqs.(43)–(48)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P44

noncomputable section

open MeasureTheory

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Claimed50.P44

open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify physicalCovariance pureCovariance)

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF p.5, Eqs.(43)-(48): unsquared off-boundary stationary equations,
conditional recovery and necessary squared elimination; on xy=1 use x nonzero
and the degree-at-most-four boundary polynomial. Denominator-zero and zero
polynomial cases are retained; no complete isolated-root algorithm is asserted. -/
theorem diagonal_candidates (a b c1 c2 d1 d2 : ℝ)
    (hresource : PhysicalResource (standardCov a b c1 c2))
    (hD : InputOrProcess (!![d1, 0; 0, d2] : QuadratureMatrix)) :
    (∀ x : ℝ, 0 < firstBaseVariance a b c1 d1 x) ∧
    (∀ y : ℝ, 0 < secondBaseVariance a b c2 d2 y) ∧
    (∀ x y : ℝ, x * y ≠ 1 →
      (DiagonalStationary a b c1 c2 d1 d2 x y ↔
        let sign : ℝ := if 1 - x * y > 0 then 1 else -1
        x = sign * Real.sqrt (firstBaseVariance a b c1 d1 x / secondBaseVariance a b c2 d2 y) * (b * y - c2) ∧
        y = sign * Real.sqrt (secondBaseVariance a b c2 d2 y / firstBaseVariance a b c1 d1 x) * (b * x + c1))) ∧
    (∀ x y : ℝ, x * y ≠ 1 → DiagonalStationary a b c1 c2 d1 d2 x y →
      let L := x * (b ^ 2 - 1) + b * c1
      L ≠ 0 → y = c2 * (b * x + c1) / L ∧
        c2 ^ 2 * firstBaseVariance a b c1 d1 x = L ^ 2 *
          secondBaseVariance a b c2 d2 (c2 * (b * x + c1) / L)) ∧
    (∀ x : ℝ, x ≠ 0 →
      HasDerivAt (fun z : ℝ => firstBaseVariance a b c1 d1 z * secondBaseVariance a b c2 d2 (1 / z))
        (2 * boundaryPolynomial a b c1 c2 d1 d2 x / x ^ 3) x ∧
      (HasDerivAt (fun z : ℝ => firstBaseVariance a b c1 d1 z * secondBaseVariance a b c2 d2 (1 / z)) 0 x ↔
        boundaryPolynomial a b c1 c2 d1 d2 x = 0)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P44

end
