-- Prove2me | Theorems.Thm_ShortestGCS_Relax_remark_4_2
-- name    : ShortestGCS.Relax.remark_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:57:55.150902+00:00
-- url     : https://prove2.me/theorems/5e325566-4da4-4859-ac7d-9dfe0cb37dad
-- title:
--   Remark 4.2, p. 5 — for bounded 𝒳 the closure in the perspective is unnecessary
-- statement:
--   Let $\mathcal X \subseteq \mathbb R^n$ be a compact convex set. Then its perspective needs no closure:
--
--   $$
--   \tilde{\mathcal X} = \{(x, \lambda) : \lambda \ge 0,\ x \in \lambda\mathcal X\}.
--   $$
--
--   In particular, if $(u, 0) \in \tilde{\mathcal X}$ then $u = 0$. This is the property of bounded sets used in the proof of Lemma 7.4.
--
--   **Formalization Note** "Bounded" is encoded as compact: Definition 4.1 applies to closed sets, and a closed bounded subset of $\mathbb R^n$ is compact. For $\mathcal X = \emptyset$ both sides are empty.
-- source:
--   arXiv:2101.11565v5, Remark 4.2, p. 5

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_Relax_Setting

namespace ShortestGCS.Relax

open Pointwise

/-- Remark 4.2, arXiv:2101.11565v5, p. 5: for a bounded (here compact) convex set `𝒳`, the closure in
Definition 4.1 is unnecessary: `𝒳̃ = {(x, λ) : λ ≥ 0, x ∈ λ𝒳}`. -/
theorem remark_4_2 {n : ℕ} (X : Set (Fin n → ℝ)) (hXc : IsCompact X) (hXcv : Convex ℝ X) :
    ShortestGCS.MICP.perspectiveSet X = {q : (Fin n → ℝ) × ℝ | 0 ≤ q.2 ∧ q.1 ∈ q.2 • X} := by sorry

end ShortestGCS.Relax
