-- Prove2me | Theorems.Thm_RadGauss_Structural_theorem_12_part_3
-- name    : RadGauss.Structural.theorem_12_part_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T15:49:47.148263+00:00
-- url     : https://prove2.me/theorems/96ae5d0b-6e97-4bc8-a0b1-3c9be97026d3
-- title:
--   Theorem 12, part 3 — R_n(cF) = |c| R_n(F) for every real c
-- statement:
--   **Theorem 12, part 3 (Bartlett–Mendelson 2002, p. 469).** Let $\mu$ be a probability measure on $\mathcal X$, $n\ge0$ an integer, and $R_n$ the Rademacher complexity of Definition 2. For a class $F$ of real functions on $\mathcal X$ and a real number $c$, write $cF=\{cf : f\in F\}$. Then for every $c\in\mathbb R$,
--
--   $$
--   R_n(cF)=|c|\,R_n(F).
--   $$
--
--   The Rademacher complexity is thus absolutely homogeneous; in particular $R_n(-F)=R_n(F)$.
--
--   **Formalization Note** Complexities lie in $[0,\infty]$ and $|c|$ is embedded as `ENNReal.ofReal |c|`. With the convention $0\cdot\infty=0$ the case $c=0$ is consistent: $0F$ is $\{0\}$ (or empty if $F$ is), whose complexity is $0$, even when $R_n(F)=\infty$.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 469 (PDF p. 7), Theorem 12, part 3

import Mathlib
import Definitions.Def_RadGauss_RiskBound_rademacherComplexity

open MeasureTheory
open scoped ENNReal Pointwise

namespace RadGauss.Structural

/-- **Theorem 12, part 3** (Bartlett–Mendelson, JMLR 3 (2002), p. 469): for every `c ∈ ℝ`,
`R_n(cF) = |c| R_n(F)`, where `cF = {c f : f ∈ F}`. -/
theorem theorem_12_part_3 {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (n : ℕ) (F : Set (X → ℝ)) (c : ℝ) :
    RadGauss.RiskBound.rademacherComplexity μ n (c • F) = ENNReal.ofReal |c| * RadGauss.RiskBound.rademacherComplexity μ n F := by sorry

end RadGauss.Structural
