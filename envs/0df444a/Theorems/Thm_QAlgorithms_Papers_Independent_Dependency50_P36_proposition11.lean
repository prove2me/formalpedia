-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P36_proposition11
-- name    : QAlgorithms.Papers.Independent.Dependency50.P36.proposition11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:41:13.580831+00:00
-- url     : https://prove2.me/theorems/4ecab649-1416-45de-800b-1413e7de28f2
-- title:
--   Isotropic-state distillation via an LP
-- statement:
--   Let $d\ge2$, $n\ge1$, $0\le F\le1$ and $0\le\varepsilon<1$. With $\Psi_d=d^{-1}\sum_{i,j}|ii\rangle\langle jj|$, define $\rho_F=F\Psi_d+(1-F)(I-\Psi_d)/(d^2-1)$. For $0\le i,k\le n$ set
--
--   $$x_{i,k}=d^{-n}\sum_{m=\max(0,i+k-n)}^{\min(i,k)}\binom{k}{m}\binom{n-k}{i-m}(-1)^{i-m}(d-1)^{k-m}(d+1)^{n-k+m-i}.$$
--
--   The minimum $\eta_0$ over real $\eta,m_0,\ldots,m_n$ subject to
--
--   $$0\le m_i\le1,\quad\sum_{i=0}^n\binom ni F^i(1-F)^{n-i}m_i\ge1-\varepsilon,\quad-\eta\le\sum_{i=0}^n x_{i,k}m_i\le\eta\quad(0\le k\le n)$$
--
--   is attained and positive, and
--
--   $$E_{D,\mathrm{PPT}}^{(1),\varepsilon}(\rho_F^{\otimes n})=\log_2\lfloor1/\eta_0\rfloor.$$
--
--   PPT operations are completely PPT-preserving CPTP maps on the grouped Alice:Bob cut; fidelity to the positive-integer-rank target is squared fidelity. Only minimizing $\eta$ is linear; the last formula is postprocessing.
-- source:
--   Non-asymptotic entanglement distillation, arXiv:1706.06221v3, PDF p. 10, Proposition 11, Eqs. (53)–(54): n-fold isotropic-state linear program

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P36

open QAlgorithms.Papers.Independent.Information100.P03 (partialTransposeB)

open QAlgorithms.Papers.Independent.Information100.P04 (copies)

open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P34 (dephasing)

open QAlgorithms.Papers.Independent.Information100.P63 (testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- Proposition 11, arXiv:1706.06221v3, PDF pp.10–11, Eqs.(53)–(54).
Minimizing eta is an LP; log floor(1/eta) is nonlinear postprocessing. -/
theorem proposition11 (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (F epsilon : ℝ) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (he0 : 0 ≤ epsilon) (he1 : epsilon < 1) :
    ∃ eta : ℝ, ∃ m : Fin (n + 1) → ℝ, 0 < eta ∧
      isotropicLPFeasible d n F epsilon eta m ∧
      (∀ z : ℝ, ∀ u : Fin (n + 1) → ℝ,
        isotropicLPFeasible d n F epsilon z u → eta ≤ z) ∧
      oneShot .ppt (copies (overlapIsotropic d F) n) epsilon =
        (log2 (Nat.floor eta⁻¹) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P36

end
