-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P95_operator_pushing
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P95.operator_pushing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:43:30.506364+00:00
-- url     : https://prove2.me/theorems/057725a4-7c20-4556-b99c-18624de2ade2
-- title:
--   Operator pushing preserves the operator norm
-- statement:
--   Let $T:\mathcal H_A\to\mathcal H_B$ be an isometry between finite-dimensional complex Hilbert spaces, and let $O$ be any linear operator on $\mathcal H_A$. Define $O_{\mathrm{out}}=TOT^\dagger$. Then
--
--   $$TO=O_{\mathrm{out}}T,\qquad \|O_{\mathrm{out}}\|_{2\to2}=\|O\|_{2\to2}.$$
--
--   Thus every incoming operator has an explicit outgoing representative with the same Hilbert-space operator norm. Orthonormal computational bases identify the maps with their matrices.
-- source:
--   Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence, arXiv:1503.06237v2, PDF p. 6, §2, operator pushing (2.3)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P95

namespace QAlgorithms.Papers.Independent.Intakenext100.P95

open scoped Matrix ComplexConjugate

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF p.6, (2.3): the explicit pushed operator intertwines and has the same L2
operator norm. The norm is that of the continuous map on Euclidean Hilbert space. -/
theorem operator_pushing {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (T : Matrix B A ℂ) (hT : Tᴴ * T = 1)
    (O : Matrix A A ℂ) :
    T * O = (T * O * Tᴴ) * T ∧
    ‖Matrix.toEuclideanCLM (n := B) (𝕜 := ℂ) (T * O * Tᴴ)‖ =
      ‖Matrix.toEuclideanCLM (n := A) (𝕜 := ℂ) O‖ := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P95
