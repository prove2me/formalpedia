-- Prove2me | Theorems.Thm_TensorNP_Eigen_colorTensor_canonical_encoder
-- name    : TensorNP.Eigen.colorTensor_canonical_encoder
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-01T19:13:27.837074+00:00
-- url     : https://prove2.me/theorems/3f5bdfa5-ba1a-47cc-841b-d164b840063b
-- title:
--   A polynomial-time canonical encoder for the graph-to-tensor construction
-- statement:
--   There exists a single total polynomial-time Cook-style Turing machine computing a function $f$ on arbitrary strings over the fixed four-symbol coding alphabet such that:
--
--   * If the input is the canonical binary adjacency-matrix code of a finite simple graph $G$, then $f$ outputs the canonical rational tensor code of the explicitly constructed tensor $T_G$.
--   * If the input is not the canonical code of any finite simple graph, then $f$ outputs the empty string.
--
--   This is the concrete parsing, validation, tensor emission, and polynomial-runtime obligation in the graph 3-colorability reduction. The empty fallback is a non-instance of the target language. The result concerns actual execution on the specified one-tape machine model; output-size estimates alone do not establish it.
--
--   **Formalization Note.** The finite graph and rational-tensor code formats, as well as the one-tape execution convention, are the platform’s explicit choices for realizing the construction of Hillar and Lim.
-- source:
--   Hillar and Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6), 2013, Definition 2.9 and proof of Theorem 1.3, https://arxiv.org/abs/0911.1393 ; source-specific machine realization for the platform encoding.

import Definitions.Def_TensorNP_Eigen_Construction

namespace TensorNP.Eigen

open CookPvsNP ProjSchedTW.Complexity

/-- A total Cook-polynomial machine writes the precise tensor code of every
    canonical graph input and the empty string on every non-graph input. -/
theorem colorTensor_canonical_encoder :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      (∀ (v : ℕ) (G : SimpleGraph (Fin v)), f (graphCode G) = tensorCode (colorTensor G)) ∧
      (∀ w, (¬ ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = graphCode G) → f w = []) := by sorry

end TensorNP.Eigen
