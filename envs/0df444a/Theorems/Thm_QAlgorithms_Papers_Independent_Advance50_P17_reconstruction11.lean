-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P17_reconstruction11
-- name    : QAlgorithms.Papers.Independent.Advance50.P17.reconstruction11
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T11:26:20.657984+00:00
-- url     : https://prove2.me/theorems/15182231-0f51-4e25-8cb6-6f82a147ec7f
-- title:
--   Section IV A, Eq.(11): reconstruction from input states and observables
-- statement:
--   Let $d\ge1$, $\mathcal E$ be CPTP, and $U$ be a unitary on the $d$-dimensional register. Choose $d^2$ unitaries $V_j$ with $\operatorname{tr}(V_j^\dagger V_k)=d\delta_{jk}$, a density-matrix operator basis $\rho_k$, and a Hermitian operator basis $\sigma_l$. Compute $a_{jk}$ and $b_{jl}$ by $V_j=\sum_k a_{jk}\rho_k$ and $UV_j^\dagger U^\dagger=\sum_l b_{jl}\sigma_l$, and put $M_{kl}=\sum_j b_{jl}a_{jk}$. Then
--
--   $$F_{\rm pro}(\mathcal E,U)=d^{-3}\sum_{k,l}M_{kl}\operatorname{tr}(\sigma_l\mathcal E(\rho_k)).$$
--
--   The equality is interpreted in $\mathbb C$, with real left side. The $d^4$ indexed observable averages determine the fidelity, and their coefficients are independent of $\mathcal E$. The adjoint in the definition of $b$ corrects the expansion printed before (11), as required by (10).
-- source:
--   Distance measures to compare real and ideal quantum processes, arXiv:quant-ph/0408063v2, PDF p. 6, Section IV A, Eq.(11): reconstruction from input states and observables

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P17

noncomputable section

open MeasureTheory Filter

open scoped Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Advance50.P17

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P75 (hermitianReal)

variable {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]
  [Nonempty I] [Nonempty J] [Nonempty K]

/-- Section IV A, PDF p.6, Eq.(11): d^4 expectation values suffice.
PRINTED: b expands U V_j U^dagger. CHANGED: expand U V_j^dagger U^dagger,
as required by Eq.(10). Coefficients are computed from bases, never assumed to fit E. -/
theorem reconstruction11 (E : FiniteProcess I I) (U : Matrix.unitaryGroup I ℂ)
    (V : I × I → Matrix.unitaryGroup I ℂ)
    (hv : ∀ j k, ((V j : Matrix I I ℂ)ᴴ * (V k : Matrix I I ℂ)).trace =
      if j = k then (Fintype.card I : ℂ) else 0)
    (r s : Module.Basis (I × I) ℂ (Matrix I I ℂ))
    (hr : ∀ k, IsDensityMatrix (r k)) (hs : ∀ l, (s l).IsHermitian) :
    (proFidelity E.val (conjSuperop (U : Matrix I I ℂ)) : ℂ) =
      (Fintype.card I : ℂ)⁻¹ ^ 3 *
        ∑ k, ∑ l, reconstructionCoefficients r s V U k l * (s l * E.val (r k)).trace ∧
    Fintype.card ((I × I) × (I × I)) = Fintype.card I ^ 4 := by sorry

end QAlgorithms.Papers.Independent.Advance50.P17

end
