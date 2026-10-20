-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P30_flower_locking
-- name    : QAlgorithms.Papers.Independent.Frontier30.P30.flower_locking
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:30:51.674472+00:00
-- url     : https://prove2.me/theorems/3f3bcd23-bbf1-41e7-8f49-73d15c832160
-- title:
--   One-qubit locking of formation, operational cost, and logarithmic negativity
-- statement:
--   Let $\ell\ge0$ be an integer, $d=2^\ell$, and $U=H^{\otimes\ell}$ for the normalized Hadamard matrix $H$. Let $\rho_\ell$ be the density matrix in (1), equivalently the reduction of purification (2), on $(\mathbb C^2\otimes\mathbb C^d)_A\otimes(\mathbb C^2\otimes\mathbb C^d)_B$. Write $\mathcal D_A$ for complete computational dephasing of Alice's flag qubit with outcome forgotten. Formation $E_F$ is the infimum over all finite normalized pure ensembles, $E_c$ is the asymptotic singlet formation cost under evaluated finite LOCC with vanishing full trace-norm error, and $E_N(\rho)=\log_2\|\rho^{\Gamma_A}\|_1$. Then
--
--   $$E_F(\rho_\ell)\ge\frac\ell2,\qquad E_c(\rho_\ell)\ge\frac\ell2,\qquad E_N(\rho_\ell)=\log_2(\sqrt d+1).$$
--
--   Moreover $\mathcal D_A(\rho_\ell)$ is separable and all three measures on it equal zero. Varying $\ell$ gives arbitrarily large losses caused by one local qubit measurement.
-- source:
--   Locking entanglement measures with a single qubit, arXiv:quant-ph/0404096v1, PDF p. 1, Eqs. (1)–(3), continuation on p.2

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P30

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

/-- arXiv:quant-ph/0404096v1, PDF pp.1--2, (1)--(3) and first paragraph of p.2.
Purification (2) corrects printed local dimension d+2 to 2d. Only the source's
lower bounds on formation and operational cost are asserted. ell=0 is retained. -/
theorem flower_locking (ell : ℕ) :
    IsDensityMatrix (flower ell) ∧
    (ell : ℝ)/2 ≤ Information100.P08.formation (flower ell) ∧
    (ell : ℝ)/2 ≤ operationalEc (flower ell) ∧
    flaggedLogNegativity (flower ell) = log2 (Real.sqrt ((2^ell : ℕ) : ℝ)+1) ∧
    Entanglement.IsSeparableDensity (dephaseFlag (flower ell)) ∧
    Information100.P08.formation (dephaseFlag (flower ell)) = 0 ∧
    operationalEc (dephaseFlag (flower ell)) = 0 ∧
    flaggedLogNegativity (dephaseFlag (flower ell)) = 0 := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P30

end
