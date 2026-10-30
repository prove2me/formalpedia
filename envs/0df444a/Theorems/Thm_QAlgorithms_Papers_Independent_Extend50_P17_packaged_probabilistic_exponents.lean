-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P17_packaged_probabilistic_exponents
-- name    : QAlgorithms.Papers.Independent.Extend50.P17.packaged_probabilistic_exponents
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:57:07.805995+00:00
-- url     : https://prove2.me/theorems/33f88fdd-784a-4be8-87f4-6c196a78b4b3
-- title:
--   Table 3: packaged probabilistic critical exponents
-- statement:
--   Let $N_t\to\infty$ and $1\le k_t\le N_t$ be integer schedules with $k_t\mid N_t$ eventually and $k_t/N_t^\alpha\to a>0$, where $\alpha\le1$. In qubit packaged protocols, success requires every package to succeed. Let $p_{\rm pack}$ use fixed EPR resources and optimal conclusive measurements, while $p_{\rm pack}^{\rm OPBT}$ additionally optimizes each package's resource. With $c=\sqrt{8/\pi}$,
--
--   $$\lim p_{\rm pack}=\begin{cases}1&\alpha<1/3,\\e^{-ca^{3/2}}&\alpha=1/3,\\0&\alpha>1/3,\end{cases}\qquad\lim p_{\rm pack}^{\rm OPBT}=\begin{cases}1&\alpha<1/2,\\e^{-3a^2}&\alpha=1/2,\\0&\alpha>1/2.\end{cases}$$
--
--   This includes the physical $\alpha=1$ zero-limit case and makes no claim for an unphysical superlinear number of output systems.
-- source:
--   Multiport based teleportation -- transmission of a large amount of quantum information, arXiv:2008.00856v3, PDF p. 6, Table 3: packaged probabilistic critical exponents

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P17

open Filter MeasureTheory

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

/-- PDF p.6, Table 3: packaged probabilistic exponents in the physical range alpha≤1. -/
theorem packaged_probabilistic_exponents (N k : ℕ → ℕ) (a alpha : ℝ)
    (hsch : PackageSchedule N k) (ha : 0 < a)
    (hphysical : alpha ≤ 1) (hscale : Scales N k a alpha) :
    RegimeLimit N k packagedSuccess alpha (1/3)
      (Real.exp (-Real.sqrt (8/Real.pi) * a^(3/2 : ℝ))) ∧
    RegimeLimit N k packagedOptimalSuccess alpha (1/2)
      (Real.exp (-3*a^2)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P17

end
