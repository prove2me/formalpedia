-- Prove2me | Theorems.Thm_ProgHedging_Convex_proposition_3_3
-- name    : ProgHedging.Convex.proposition_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:33.784798+00:00
-- url     : https://prove2.me/theorems/8f456c42-48f6-4487-8547-da4aa76ec1be
-- title:
--   Proposition 3.3 — 𝒞 is nonempty and closed, F is locally Lipschitz, and the level sets of F on 𝒞 are compact
-- statement:
--   In problem (P), the admissible set $\mathcal C=\{X\mid X(s)\in C_s\ \forall s\}$ is nonempty and closed, the objective $F(X)=\sum_s p_sf_s(X(s))$ is locally Lipschitz continuous on the policy space $\mathcal E$, and every level set
--
--   $$
--   \{X\in\mathcal C\mid F(X)\le\alpha\},\qquad \alpha\in\mathbb R,
--   $$
--
--   is compact.
--
--   This transfers the standing assumptions on the scenario data to the full problem, and yields existence of optimal solutions of (P) whenever it is feasible.
--
--   **Formalization Note.** The printed statement breaks off after "all level sets of the form (3.8)" without a predicate; its proof ends "It follows that any set (3.8) is compact", which is the reading formalized. Local Lipschitz continuity and compactness use Mathlib's (product) topology on policies, which in finite dimension is the topology of the paper's norm.
-- source:
--   Rockafellar and Wets, Scenarios and policy aggregation in optimization under uncertainty, IIASA Working Paper WP-87-119 (1987), p. 13, Proposition 3.3, (3.8), and its proof

import Mathlib
import Definitions.Def_ProgHedging_Convex_Problem

open scoped RealInnerProductSpace Pointwise Topology
open Filter

namespace ProgHedging.Convex

/-- Proposition 3.3, p. 13 (with the conclusion of its proof: the level sets are compact).
The feasible set `𝒞` of (P) is nonempty and closed, `F` is locally Lipschitz on `ℰ`, and every level
set `{X ∈ 𝒞 | F(X) ≤ α}` is compact. -/
theorem proposition_3_3 {S : Type*} [Fintype S] {n T : ℕ} (pr : Problem S n T) :
    pr.adm.Nonempty ∧ IsClosed pr.adm ∧ LocallyLipschitz pr.F ∧
    ∀ α : ℝ, IsCompact {X | X ∈ pr.adm ∧ pr.F X ≤ α} := by sorry

end ProgHedging.Convex
