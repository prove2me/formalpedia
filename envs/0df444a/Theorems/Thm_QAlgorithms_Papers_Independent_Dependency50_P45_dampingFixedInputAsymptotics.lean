-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P45_dampingFixedInputAsymptotics
-- name    : QAlgorithms.Papers.Independent.Dependency50.P45.dampingFixedInputAsymptotics
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:08:00.78416+00:00
-- url     : https://prove2.me/theorems/7d39957a-183a-476d-865a-aca3d5021490
-- title:
--   §III.B Eqs.(88),(90): fixed-input asymptotics
-- statement:
--   Let $x\in(0,1)$ be fixed. For amplitude damping $\mathcal D_p$, define $J_E(p,x)=h_2(x)+h_2((1-p)x)-h_2(px)$. Let $\rho_{x,\pm}$ have diagonal $(1-x,x)$ and off-diagonal entries $\pm\sqrt{x(1-x)}$, and put $J_H(p,x)=H(\mathcal D_p(\rho_x))-\tfrac12 H(\mathcal D_p(\rho_{x,+}))-\tfrac12 H(\mathcal D_p(\rho_{x,-}))$. All entropies and logarithms are in bits. As $p\uparrow1$ through $0\le p<1$,
--
--   $$\frac{J_E(p,x)}{-x(1-p)\log_2(1-p)}\longrightarrow1,\qquad \frac{J_H(p,x)}{-x(1-x)(1-p)\log_2(1-p)}\longrightarrow1.$$
--
--   These are the fixed-input objectives in Eqs.(88),(90). The subsequent optimization on p.35 is separate; these formulas are not capacities at every free value of $x$.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, PDF p. 34, §III.B Eqs.(88),(90): fixed-input asymptotics

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF p.34, Eqs.(88),(90): fixed-x objectives, with base-two logarithms.
The one-sided punctured limit excludes the p=1 quotient default. -/
theorem dampingFixedInputAsymptotics (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun p => dampingEAObjective p x / (-x * (1 - p) * Real.logb 2 (1 - p)))
      (nhdsWithin 1 (Set.Ico (0 : ℝ) 1)) (nhds 1) ∧
    Tendsto (fun p => dampingHolevoObjective p x /
      (-x * (1 - x) * (1 - p) * Real.logb 2 (1 - p)))
      (nhdsWithin 1 (Set.Ico (0 : ℝ) 1)) (nhds 1) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P45

end
