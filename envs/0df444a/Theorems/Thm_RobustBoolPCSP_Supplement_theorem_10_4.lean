-- Prove2me | Theorems.Thm_RobustBoolPCSP_Supplement_theorem_10_4
-- name    : RobustBoolPCSP.Supplement.theorem_10_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:41:03.265496+00:00
-- url     : https://prove2.me/theorems/903af71f-a9e8-403f-8a07-7ec1cc8111a9
-- title:
--   Theorem 10.4 (Dimension-uniform Gaussian lower bound) — $(A+E+N)/3\ge c_*v/\log^2(e/v)$
-- statement:
--   There is an absolute constant $c_*>0$ such that for every dimension $d$, every $0<v\le1/4$ and all measurable fuzzy colorings $F:\mathbb R^d\to\Delta(\mathbb Z/5\mathbb Z)$, $G:\mathbb R^{2d}\to\Delta(\mathbb Z/5\mathbb Z)$, the antipodal, erasure and equality costs of §10.2 satisfy
--
--   $$\frac{A+E+N}3\ge\frac{c_*v}{\log^2(e/v)}.$$
--
--   The bound is uniform in $d$; it is the Gaussian input to the obstruction for $\Lambda^{=}$.
--
--   Differences from the source:
--   - encoding: ℝ^{2d} → Fin (d + d) → ℝ, with (−W, H₀) as Fin.append; reason: same space
--   - encoding: costs as rejection probabilities → integrals of bounded measurable integrands against standard Gaussian product measures; reason: exact expectations
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), Theorem 10.4, p.84

import Mathlib
import Definitions.Def_RobustBoolPCSP_Supplement_GaussianTests

set_option autoImplicit false

namespace RobustBoolPCSP.Supplement

/-- **Theorem 10.4 (Dimension-uniform Gaussian lower bound)**, p.84. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"There is an absolute c∗ > 0 such that, for every d, every 0 < v ≤ 1/4, and all measurable fuzzy
F, G above, (A + E + N)/3 ≥ c∗v/log²(e/v). (94)" Setting (§10.2, p.83): `B = Z/5Z`, `H` the five-cycle,
`F : R^d → ∆(B)`, `G : R^{2d} → ∆(B)` measurable, and the antipodal, erasure and equality costs
`A`, `E`, `N` with (93).

**Formalization Note.** `A, E, N` are `costA`, `costE`, `costN` (rejection probabilities, as
integrals of bounded measurable functions against standard Gaussian measures); `ℝ^{2d}` is
`Fin (d + d) → ℝ`. `log²(e/v) = (Real.log (e/v))²`. `c∗` comes before `d`, `v`, `F`, `G`. -/
theorem theorem_10_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ) (v : ℝ), 0 < v → v ≤ 1 / 4 →
      ∀ (F : (Fin d → ℝ) → ZMod 5 → ℝ) (G : (Fin (d + d) → ℝ) → ZMod 5 → ℝ),
        IsFuzzy F → IsFuzzy G →
          c * v / (Real.log (Real.exp 1 / v)) ^ 2 ≤ (costA F + costE v F G + costN v G) / 3 := by sorry

end RobustBoolPCSP.Supplement
