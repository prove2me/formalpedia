-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P61_tensor_factor_lower
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P61.tensor_factor_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:11:19.921266+00:00
-- url     : https://prove2.me/theorems/e527b86c-640c-45eb-bcdb-6ccf8b64cf58
-- title:
--   Lemma 6: tensor-factor lower bound
-- statement:
--   For arbitrary finite-dimensional density matrices $\tau,\omega$ and $0\le\varepsilon<1$, let $\Delta_e$ denote the logarithm of the joint retained-subset minimum $|J|\max_{j\in J}r_j$, with retained mass at least $1-e$. Then
--
--   $$\Delta_\varepsilon(\tau\otimes\omega)\ge\Delta_{\sqrt\varepsilon}(\tau)+\log_2(1-\sqrt\varepsilon).$$
--
--   No purity or flatness assumption is imposed on the auxiliary density $\omega$. This bounds a tensor product's smooth spread using one factor.
-- source:
--   On the communication cost of entanglement transformations, arXiv:quant-ph/0204092v3, PDF p. 4, Lemma 6: tensor-factor lower bound

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P61

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P61

open scoped Matrix ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Dependency50.P35 (supportRank)

open QAlgorithms.Papers.Independent.Bridge50.P40 (entropyInfinity)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

attribute [local instance] Classical.propDecidable

section SpectralResults

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- PDF p.4, Lemma 6: arbitrary auxiliary density, including epsilon=0. -/
theorem tensor_factor_lower (tau : Matrix I I ℂ) (omega : Matrix J J ℂ)
    (htau : IsDensityMatrix tau) (homega : IsDensityMatrix omega)
    (epsilon : ℝ) (hzero : 0 ≤ epsilon) (hone : epsilon < 1) :
    smoothSpread tau (Real.sqrt epsilon) + logTwo (1 - Real.sqrt epsilon) ≤
    smoothSpread (Matrix.kronecker tau omega) epsilon := by sorry

end SpectralResults

end QAlgorithms.Papers.Independent.Intakenext100.P61

end
