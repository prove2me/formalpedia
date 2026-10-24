-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P28_regular_optimal_product_majorization
-- name    : QAlgorithms.Papers.Independent.Support50.P28.regular_optimal_product_majorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:17:04.826539+00:00
-- url     : https://prove2.me/theorems/02580612-5581-4fa3-9a45-70f5bf08ab56
-- title:
--   Proposition 1, corrected regular-case optimal-product majorization
-- statement:
--   Consider finitely many complete bosonic modes, with no photon cutoff or energy constraint. Covariances use the interleaved coordinates $(x_1,p_1,\ldots)$, $[x_j,p_j]=i$, and doubled vacuum covariance $I$. A centered Gaussian channel $\Phi_{X,Y}$ is an actual completely positive trace-preserving map, with covariance action $\gamma\mapsto X^T\gamma X+Y$ and $Y+i\sigma-iX^T\sigma X\ge0$, where $X,Y$ are real, $Y=Y^T$, and $\sigma=\bigoplus_j\left[\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right]$.
--
--   Write $\mathcal G$ for the normalized centered Gaussian densities and, for real $p>1$, put $\xi_p(\Phi)=\sup_{\rho\in\mathcal G}(\operatorname{Tr}\Phi(\rho)^p)^{1/p}$. For a finite channel family, multiplicativity means equality of the joint Gaussian-input supremum to the product of the factor suprema; joint inputs may be entangled.
--
--   This is an explicitly corrected regular-case statement. Let $\Phi=\Phi_{X,Y}$ be a single-mode Gaussian channel with $\det X\ne0$ and $Y>0$ in the strict Loewner sense. There exists a centered pure Gaussian density $\rho_0$, chosen independently of $p$ and of the number of channel uses, such that for all real $p>1$ and all integers $r\ge1$,
--
--   $$\|\Phi(\rho_0)\|_p=\xi_p(\Phi),\qquad
--   \|\Phi^{\otimes r}(\rho_0^{\otimes r})\|_p=\xi_p(\Phi^{\otimes r}),\qquad
--   \Phi(\rho_0)^{\otimes r}\succ\Phi^{\otimes r}(\rho)\quad(\rho\in\mathcal G_r).$$
--
--   Here $A\succ B$ means that for every positive integer $k$, the sum of the $k$ largest eigenvalues of $A$ is at least the corresponding sum for $B$, with multiplicities and zero padding. This identifies one product input that is optimal simultaneously for every $p>1$ and dominates every joint Gaussian output. The two regularity guards are additions to the printed unrestricted claim; the full printed claim remains deferred.
-- source:
--   Multiplicativity of maximal output purities of Gaussian channels under Gaussian inputs, arXiv:quant-ph/0406065v1, PDF p. 5, Proposition 1, corrected regular-case optimal-product majorization

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P28

noncomputable section

open scoped BigOperators ENNReal ComplexOrder Matrix

namespace QAlgorithms.Papers.Independent.Support50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel rankOne)

open QAlgorithms.Papers.Independent.Claimed50.P47
  (Occupation gaussianStateCharacteristic singleCharacteristic weylKernel)

open QAlgorithms.Papers.Independent.Claimed50.P30 (phiMinus)

/-- PDF p.5, corrected regular-case Proposition 1: det X != 0 and Y positive
definite are ADDED guards, as explicitly inventoried in the plan. The printed
unrestricted optimizer assertion is false and remains in HARD.md. One pure
one-mode input works for all p>1 and all tensor powers; comparison is against
every Gaussian joint input, including entangled and mixed ones. -/
theorem regular_optimal_product_majorization (E : CenteredOscillatorChannel (Fin 1))
    (hX : E.X.det ≠ 0) (hY : E.Y.PosDef) :
    ∃ rho0 : State (Occupation (Fin 1)), IsCenteredGaussianDensity rho0 ∧ IsPureOscillatorDensity rho0 ∧
      (∀ p : ℝ, 1 < p → pNorm p (E.map rho0.coefficients) = maximalOutputPurity p E.map) ∧
      ∀ r : ℕ, 0 < r →
        (∀ p : ℝ, 1 < p →
          pNorm p (tensorOscillatorChannel (m := fun _ : Fin r => 1) (fun _ => E)
            (productInput (m := fun _ : Fin r => 1) (fun _ => rho0))) =
          maximalOutputPurity p (tensorOscillatorChannel (m := fun _ : Fin r => 1) (fun _ => E))) ∧
        ∀ rho : State (Occupation (Σ _ : Fin r, Fin 1)), IsCenteredGaussianDensity rho →
          OscillatorMajorizes
            (tensorOscillatorChannel (m := fun _ : Fin r => 1) (fun _ => E)
              (productInput (m := fun _ : Fin r => 1) (fun _ => rho0)))
            (tensorOscillatorChannel (m := fun _ : Fin r => 1) (fun _ => E) rho.coefficients) := by sorry

end QAlgorithms.Papers.Independent.Support50.P28

end
