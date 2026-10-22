-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_choi_basis_change
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.choi_basis_change
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T22:31:02.22153+00:00
-- url     : https://prove2.me/theorems/437b0e3a-fd60-45a8-9be0-ddc219549f65
-- title:
--   Lemma 2.11.
-- statement:
--   All spaces are finite-dimensional over the complex numbers, with their indicated computational bases. Choi matrices are unnormalized and ordered output tensor input.
--
--   Let $\Phi:\mathcal L(\mathbb C^{d_{\rm in}})\to\mathcal L(\mathbb C^{d_{\rm out}})$ be complex-linear and let $V,W$ be arbitrary square input and output matrices. For $\Phi'(X)=W^\dagger\Phi(VXV^\dagger)W$,
--   $$J(\Phi')=(W\otimes\overline V)^\dagger J(\Phi)(W\otimes\overline V).$$
--   No unitarity or invertibility is assumed.
--
--   This is the stated interface for the corresponding result of the paper.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 16, Lemma 2.11.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.16, Lemma 2.11: V and W are arbitrary matrices; the bar is on V. -/
theorem choi_basis_change (din dout : ℕ)
    (Phi : Op (Fin din) →ₗ[ℂ] Op (Fin dout)) (V : Op (Fin din)) (W : Op (Fin dout)) :
    functionOutputChoi (fun rho => Wᴴ * Phi (V * rho * Vᴴ) * W) =
      (Matrix.kronecker W (fun i j => conj (V i j)))ᴴ * functionOutputChoi Phi *
        Matrix.kronecker W (fun i j => conj (V i j)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
