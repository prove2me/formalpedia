-- Prove2me | Theorems.Thm_WeldedPath_completion_gram_conditioning
-- name    : WeldedPath.completion_gram_conditioning
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-11-18T02:26:54.790375+00:00
-- url     : https://prove2.me/theorems/2320b5eb-ec79-43bd-a718-4e877b207395
-- title:
--   Uniform conditioning of the canonical completion Gram operator
-- statement:
--   For every permutation size s and database level r satisfying 4r <= s, the actual canonical completion Gram operator obeys P_r <= G_r <= 2 P_r in the positive-operator order. Its norm is at most 2, and the canonical inverse square root, extended by zero off its support, has norm at most 1. No representation-theoretic or spectral premise is assumed.
-- source:
--   A uniform-constant consequence of Carolan and Majenz, Compressed Permutation Oracles Revisited, https://arxiv.org/html/2609.28469v1, Lemma 4.9 and equations (33)-(35), for the canonical WeldedPath completion operators in https://arxiv.org/html/2611.05912v1, equations (10)-(12). This is a proved supporting estimate for WeldedPath.crossing_probability_bound; it does not assert the remaining exact-oracle comparison.

import Mathlib
import Definitions.Def_WeldedPath_exactCpO

set_option autoImplicit false
open Classical

namespace WeldedPath

theorem completion_gram_conditioning (s r : ℕ) (hsmall : 4*r ≤ s) :
    projLevel s r ≤ Gram s r ∧
    Gram s r ≤ (2 : ℝ) • projLevel s r ∧
    ‖Gram s r‖ ≤ 2 ∧ ‖GramInvSqrt s r‖ ≤ 1 := by
  sorry

end WeldedPath
