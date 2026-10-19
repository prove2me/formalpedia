-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_code_output_charge
-- name    : QAlgorithms.Papers.Independent.Information100.P62.code_output_charge
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T22:00:14.879159+00:00
-- url     : https://prove2.me/theorems/8f00e951-9d1b-42ea-aefd-d1e9b5013729
-- title:
--   Lemma 5.7: output-projection charge of a quantum code
-- statement:
--   Let $C\subseteq(\mathbb C^3)^{\otimes n}$ be a nonzero correctable subspace of dimension $q$ for the constructed $\Phi^{\otimes n}$, with orthogonal projection $P_C$ and $P_CM_yP_C=\lambda_yP_C$, $\lambda_y\ge0$. With $E_y,M_y,\Pi$ from (5.22),(5.27) and $Q_C=\sum_{\lambda_y>0}\lambda_y^{-1}E_yP_CE_y^*$,
--   $$q\le2^n,\qquad\operatorname{Tr}(Q_C\Pi)=\sum_{\lambda_y>0}\lambda_y^{-1}\operatorname{Tr}(P_CM_y^2)\ge s_n(q).$$
--   The projections are constructed from the code and source Kraus operators; zero coefficients are excluded before inversion.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 51, Lemma 5.7: output-projection charge of a quantum code

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.51, Lemma 5.7: output-projection charge of a quantum code. -/
theorem code_output_charge (n : ℕ) (hn : 1 ≤ n)
    (C : Submodule ℂ (EuclideanSpace ℂ (Fin n → Fin 3)))
    (hC : 0 < Module.finrank ℂ C) (lam : Qubits n → ℝ)
    (hlam : ∀ y, 0 ≤ lam y)
    (hcode : ∀ y, projection C * cubeEffect y * projection C = (lam y : ℂ) • projection C) :
    Module.finrank ℂ C ≤ 2 ^ n ∧
    (Matrix.trace (cubeOutput (projection C) lam * cubePi n)).re =
      ∑ y ∈ univ.filter (fun y => 0 < lam y), (lam y)⁻¹ * (Matrix.trace (projection C * (cubeEffect y) ^ 2)).re ∧
    (charge n (Module.finrank ℂ C) : ℝ) ≤ (Matrix.trace (cubeOutput (projection C) lam * cubePi n)).re := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
