-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P30_ghz_to_star
-- name    : QAlgorithms.Papers.Independent.Intake100.P30.ghz_to_star
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:51:16.720078+00:00
-- url     : https://prove2.me/theorems/b85940e6-4a5b-43ea-aab9-ce8ee90a37aa
-- title:
--   IV.E: finite-squeezing GHZ-to-star graph transformation
-- statement:
--   Let $N\ge2$ and $G=I-J$, where $J$ is the all-ones matrix on a distinguished central mode and $N-1$ outer modes. For $\alpha>0$, write $\epsilon=e^{-2\alpha}$ and $d=1+(N-1)\epsilon^N$. The initial graph is $i\epsilon[I+(e^{2\alpha N}-1)J/N]$. Fourier transforming the distinguished mode gives a graph with central diagonal $t'$, all central links $r'$, outer diagonal $W'$, and outer off-diagonal entries $w'$:
--
--   $$t'=\frac{iN\epsilon^{N-1}}d,\quad r'=\frac{-1+\epsilon^N}d,\quad W'=\frac{i\epsilon[2+(N-2)\epsilon^N]}d,\quad w'=\frac{i\epsilon(1-\epsilon^N)}d.$$
--
--   As $\alpha\to+\infty$ this tends to the zero-diagonal star graph with every central edge equal to $-1$. These exact finite formulas distinguish the physical intermediate states.
-- source:
--   Graphical calculus for Gaussian pure states, arXiv:1007.0725v3, PDF p. 16, IV.E: finite-squeezing GHZ-to-star graph transformation

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P30

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.Frobenius Topology

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase complexify sigma)

namespace QAlgorithms.Papers.Independent.Intake100.P30

open QAlgorithms.Papers.Independent.Claimed50.P41
  (Schrodinger gaussianWave IsCenteredGaussianFunction quadratureFunction waveMean waveCovariance displacedFunction IsImplementer)

/-- PDF pp.16–17, (4.20)–(4.29): finite GHZ-to-star conversion.
There is at least one outer node, so N>=2. The outer exp(-2 alpha)
in (4.20) multiplies the whole parenthesis. -/
theorem ghz_to_star {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J] :
    let N : ℕ := Fintype.card J + 1
    let G : Matrix (Unit ⊕ J) (Unit ⊕ J) ℝ := 1 - (fun _ _ => 1)
    (∀ alpha : ℝ, 0 < alpha →
      let eps := Real.exp (-2*alpha)
      let den := 1 + ((N : ℝ)-1) * eps^N
      hGraph G alpha = (Complex.I * (eps : ℂ)) •
        (1 + (((Real.exp (2*alpha*(N : ℝ)) - 1) / (N : ℝ) : ℝ) : ℂ) • (fun _ _ => 1)) ∧
      oneAction 0 (-1) 1 0 (hGraph G alpha) =
        oneGraph (Complex.I * (((N : ℝ) * eps^(N-1) / den : ℝ) : ℂ))
          (fun _ => (((-1 + eps^N) / den : ℝ) : ℂ))
          (fun j k => if j = k then
            Complex.I * ((eps * (2 + ((N : ℝ)-2) * eps^N) / den : ℝ) : ℂ)
            else Complex.I * ((eps * (1-eps^N) / den : ℝ) : ℂ))) ∧
    Tendsto (fun alpha => oneAction 0 (-1) 1 0 (hGraph G alpha)) atTop
      (nhds (oneGraph 0 (fun _ => -1) 0)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P30

end
