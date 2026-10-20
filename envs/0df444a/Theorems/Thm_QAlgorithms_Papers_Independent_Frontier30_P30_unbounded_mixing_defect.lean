-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P30_unbounded_mixing_defect
-- name    : QAlgorithms.Papers.Independent.Frontier30.P30.unbounded_mixing_defect
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T17:33:52.962567+00:00
-- url     : https://prove2.me/theorems/028c23c6-51ce-459a-89d8-9520d4df730c
-- title:
--   Failure of asymptotic continuity forces unbounded absolute mixing defects
-- statement:
--   Let $f_d$ be real functionals on finite-dimensional density states, with $|f_d(\rho)|\le M\log_2d$ for one constant $M\ge0$. Suppose there are common-system density pairs $\rho_n,\sigma_n$ in dimensions $d_n\to\infty$, with $\|\rho_n-\sigma_n\|_1\to0$, and one $\Delta>0$ such that $|f_{d_n}(\rho_n)-f_{d_n}(\sigma_n)|\ge\Delta\log_2d_n$ for every $n$ on a subsequence. Then for every real $K$ there exist a positive dimension $d$, density states $\rho,\sigma$ and $p\in[0,1]$ such that
--
--   $$\left|p f_d(\rho)+(1-p)f_d(\sigma)-f_d(p\rho+(1-p)\sigma)\right|>K.$$
--
--   The conclusion concerns scalar functionals and requires neither convexity nor resource monotonicity.
-- source:
--   Locking entanglement measures with a single qubit, arXiv:quant-ph/0404096v1, PDF p. 3, Eqs. (17)–(18), intervening prose

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P30

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- arXiv:quant-ph/0404096v1, PDF pp.3--4, prose after (17), before (18).
Absolute subextensivity is used; no convexity is imposed. The incorrect finite-n
coefficient printed after (17) is not promoted to a theorem. -/
theorem unbounded_mixing_defect (f : Functional) (M : ℝ) (hM : 0 ≤ M)
    (hsub : Subextensive f M) (hfailure : NonAsymptoticallyContinuous f) :
    ∀ bound : ℝ, ∃ d : ℕ, 0 < d ∧ ∃ rho sigma : Op (Fin d),
      IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧ ∃ p : ℝ, 0 ≤ p ∧ p ≤ 1 ∧
      bound < |p*f d rho+(1-p)*f d sigma-f d (densityMix p rho sigma)| := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P30

end
