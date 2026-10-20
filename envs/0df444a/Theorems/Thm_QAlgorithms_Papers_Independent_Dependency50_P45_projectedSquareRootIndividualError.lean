-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P45_projectedSquareRootIndividualError
-- name    : QAlgorithms.Papers.Independent.Dependency50.P45.projectedSquareRootIndividualError
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:03:18.742985+00:00
-- url     : https://prove2.me/theorems/8fe7347a-05bd-4e48-b507-b615023790b6
-- title:
--   §II.B Eq.(42): error for each projected square-root codeword
-- statement:
--   Let $\rho$ be a density matrix on a finite nonzero complex space $A$, with an orthonormal eigenbasis $v_a$ and eigenvalues $\lambda_a$. Let $E_b:A\to B$ be a finite normalized Kraus family, so $\sum_b E_b^\dagger E_b=I$, and write $\mathcal N(\sigma)=\sum_b E_b\sigma E_b^\dagger$. Choose an output eigenbasis for $\mathcal N(\rho)$. Fix $n\ge1$ and positive tolerances $\delta_1,\delta_2$. For each label $i$ in a finite nonempty codebook choose a supported $\delta_1$-typical input word $\alpha_i$ and Kraus word $\beta_i$, with every $\|E_{\beta_i(j)}v_{\alpha_i(j)}\|>0$. Construct normalized product outputs $t_i=\bigotimes_j E_{\beta_i(j)}v_{\alpha_i(j)}/\|E_{\beta_i(j)}v_{\alpha_i(j)}\|$. Let $P$ project onto the output $\delta_2$-frequency-typical subspace, set $\phi=\sum_i|Pt_i\rangle\langle Pt_i|$, and set $\nu_i=\phi^{-1/2}Pt_i$, with inverse zero on the kernel. Complete the effects $|\nu_i\rangle\langle\nu_i|$ by a failure outcome. With $S_{ij}=\langle t_i|P|t_j\rangle$, every label satisfies
--
--   $$P_{E,i}=1-|\langle\nu_i|t_i\rangle|^2\le2(1-S_{ii})+\sum_{j\ne i}|S_{ij}|^2.$$
--
--   Failure and every incorrect label count as error. This is a per-codeword inequality and assumes no random-code error estimates.
-- source:
--   Entanglement-assisted capacity of a quantum channel and the reverse Shannon theorem, arXiv:quant-ph/0106052v2, PDF p. 19, §II.B Eq.(42): error for each projected square-root codeword

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45

noncomputable section

open scoped ComplexConjugate Matrix

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P76 (dampingChannel)

/-- PDF p.19, Eq.(42): individual error for Kraus codewords and the output
typical projection. Every nonmatching outcome, including failure, counts as error. -/
theorem projectedSquareRootIndividualError {A B K O : Type*}
    [Fintype A] [Fintype B] [Fintype K] [Fintype O]
    [DecidableEq A] [DecidableEq B] [DecidableEq K] [DecidableEq O]
    [Nonempty A] [Nonempty B] [Nonempty K] [Nonempty O]
    (rho : Matrix A A ℂ) (hrho : IsDensityMatrix rho)
    (U : Matrix.unitaryGroup A ℂ) (lam : A → ℝ) (hspec : IsSpectralData rho U lam)
    (E : K → Matrix B A ℂ) (hE : IsKrausFamily E)
    (V : Matrix.unitaryGroup B ℂ) (mu : B → ℝ)
    (hout : IsSpectralData (krausApply E rho) V mu)
    (n : ℕ) (hn : 0 < n) (delta1 delta2 : ℝ) (hd1 : 0 < delta1) (hd2 : 0 < delta2)
    (alpha : O → Fin n → A) (beta : O → Fin n → K)
    (halpha : ∀ i, alpha i ∈ typicalWords lam n delta1)
    (hpositive : ∀ i j, 0 < ‖rectangularAct (E (beta i j))
      (WithLp.toLp 2 fun a => (U : Matrix A A ℂ) a (alpha i j))‖) :
    let t := fun i => krausWord U E (alpha i) (beta i)
    let P := typicalProjector V mu n delta2
    ∀ i, 1 - effectProb (squareRootPOVM t P (some i)) (pureDensity (t i)) ≤
      2 * (1 - (inner ℂ (t i) (act P (t i))).re) +
        ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), ‖inner ℂ (t i) (act P (t j))‖ ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P45

end
