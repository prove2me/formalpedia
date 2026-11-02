-- Prove2me | Theorems.Thm_TensorNP_Eigen_graphCode_recognizer_polytime
-- name    : TensorNP.Eigen.graphCode_recognizer_polytime
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T21:47:12.893205+00:00
-- url     : https://prove2.me/theorems/fb7cd208-c567-4a52-8056-0982945fa535
-- title:
--   Canonical graph codes have a polynomial-time characteristic function
-- statement:
--   There exists a polynomial-time function on the published four-symbol alphabet that returns the one-symbol word $[1]$ exactly on canonical encodings of finite simple graphs, and the one-symbol word $[0]$ on every other input. The encoding consists of a canonical binary vertex count followed by the row-major Boolean adjacency matrix. In particular, the empty graph is accepted and malformed or noncanonical inputs are rejected. Polynomial time is in the published one-tape Cook machine model. This is a graph-code recognizer and does not assert a graph-to-tensor reduction.
-- source:
--   Auxiliary implementation for the exact graph encoding used in the formalization of Hillar and Lim, Most Tensor Problems Are NP-Hard, J. ACM 60(6) (2013), arXiv:0911.1393v5, Theorem 1.3, pp. 0:20–0:21. The concrete recognizer is a formalization support result, not a separate theorem asserted by the paper.

import Definitions.Def_TensorNP_Eigen_Defs
open CookPvsNP ProjSchedTW.Complexity

namespace TensorNP.Eigen

theorem graphCode_recognizer_polytime :
    ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      ∀ w, (f w = [.one] ↔ ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = graphCode G) ∧
           (f w = [.zero] ↔ ¬ ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = graphCode G) := by
  sorry

end TensorNP.Eigen
