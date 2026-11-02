-- Prove2me | Theorems.Thm_TensorNP_Eigen_colorTensor_encoding_transfer
-- name    : TensorNP.Eigen.colorTensor_encoding_transfer
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-01T18:50:44.939592+00:00
-- url     : https://prove2.me/theorems/9ba06805-ba69-4d65-b7de-eb19244a0705
-- title:
--   Polynomial-time canonical graph-to-tensor encoding with sound malformed-input handling
-- statement:
--   There exists one total Cook-style polynomial-time Turing machine computing a function on arbitrary binary-alphabet strings with the following properties.
--
--   For every finite simple graph $G$ on $v$ vertices, the function maps the canonical binary adjacency-matrix code of $G$ to the canonical rational tensor code of the explicitly defined tensor $T_G$ from Hillar and Lim’s reduction.
--
--   For every input string $w$, if the output codes a tensor with real eigenvalue zero, then $w$ is the canonical code of some finite simple graph $G$ and the constructed tensor $T_G$ itself has real eigenvalue zero. This soundness condition includes malformed inputs and possible ambiguity in output decoding.
--
--   This is an encoding and machine-realization obligation, not merely an unbounded many-one reduction or a claim that output length alone implies polynomial-time computability. The chosen binary encoding and Cook machine model are explicit formalization choices.
-- source:
--   Hillar and Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6), 2013, Definition 2.9, Lemmas 2.7–2.10, and proof of Theorem 1.3; https://arxiv.org/abs/0911.1393 ; binary-code and machine realization obligation for the platform encoding.

import Definitions.Def_TensorNP_Eigen_Construction

namespace TensorNP.Eigen

open CookPvsNP ProjSchedTW.Complexity

/-- A total Cook-polynomial-time binary transformation emits the concrete graph
    tensor code and has no false positives on arbitrary input strings. -/
theorem colorTensor_encoding_transfer :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      (∀ (v : ℕ) (G : SimpleGraph (Fin v)), f (graphCode G) = tensorCode (colorTensor G)) ∧
      (∀ w, f w ∈ tensorZeroEigLangR →
        ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = graphCode G ∧
          IsEigenvalue (castTensor ℝ (colorTensor G)) 0) := by sorry

end TensorNP.Eigen
