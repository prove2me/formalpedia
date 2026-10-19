-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P62_appendix_not_algebraic_graph
-- name    : QAlgorithms.Papers.Independent.Information100.P62.appendix_not_algebraic_graph
-- status  : Open
-- author  : @Goku
-- created : 2026-10-18T22:01:52.763966+00:00
-- url     : https://prove2.me/theorems/b4a7527a-cd0d-4eea-a8ac-ba76d9970d0f
-- title:
--   Lemma B.1: dominating example outside algebraic graph class
-- statement:
--   For the channel of Appendix B.1, whose system is spanned by $\operatorname{diag}(1,1,0,0)$, $\operatorname{diag}(0,0,1,1)$, $|1\rangle\langle2|$, and $|2\rangle\langle1|$,
--   $$S_\Phi\text{ is not graph-isomorphic to any finite-dimensional star-algebra}.$$
--   The target algebra can act on any positive finite-dimensional space, and graph homomorphisms allow arbitrary finite ancillary systems.
-- source:
--   Transmitting algebras through quantum channels, arXiv:2609.40054v1, PDF p. 61, Lemma B.1: dominating example outside algebraic graph class

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

namespace QAlgorithms.Papers.Independent.Information100.P62

noncomputable section

open scoped ComplexConjugate Matrix ComplexOrder

open Finset

attribute [local instance] Classical.propDecidable

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]

variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- arXiv:2609.40054v1, PDF pp.61, 62, Lemma B.1: dominating example outside algebraic graph class. -/
theorem appendix_not_algebraic_graph :
    ∀ d : ℕ, 0 < d → ∀ S : Submodule ℂ (Matrix (Fin d) (Fin d) ℂ),
      IsAlgebra S → ¬ GraphIso (graph appendixExample) S := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P62
