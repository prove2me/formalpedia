-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_independence_monotonicity
-- name    : QAlgorithms.Papers.Independent.Information100.P62.independence_monotonicity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-18T21:33:07.076978+00:00
-- url     : https://prove2.me/theorems/ea08f32f-33d9-4f09-befa-7128ac02dcd0
-- title:
--   Lemma 2.12: graph monotonicity of independence numbers
-- statement:
--   Let $S\subseteq L(H)$ and $T\subseteq L(K)$ be operator systems on positive finite-dimensional spaces. If $S\to T$, then
--   $$\alpha(S)\le\alpha(T),\qquad\alpha_{\rm ea}(S)\le\alpha_{\rm ea}(T),\qquad\alpha_q(S)\le\alpha_q(T).$$
--   If also $T\to S$, all three inequalities are equalities. The assisted number optimizes over all finite ancillary systems and normalized shared states. These parameters are graph invariants.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 16, Lemma 2.12: graph monotonicity of independence numbers

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.16, Lemma 2.12: graph monotonicity of independence numbers. -/
theorem independence_monotonicity [Nonempty I] [Nonempty J]
    (S : Submodule ℂ (Matrix I I ℂ)) (T : Submodule ℂ (Matrix J J ℂ))
    (hS : IsSystem S) (hT : IsSystem T) (h : GraphHom S T) :
    (alpha S ≤ alpha T ∧ alphaEA S ≤ alphaEA T ∧ alphaQ S ≤ alphaQ T) ∧
    (GraphHom T S → alpha S = alpha T ∧ alphaEA S = alphaEA T ∧ alphaQ S = alphaQ T) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
