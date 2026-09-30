-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_thm54_cooperative_irreducible
-- name    : StochFictPlay.Supermodular.thm54_cooperative_irreducible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:22:00.786985+00:00
-- url     : https://prove2.me/theorems/8f1177ed-e4b9-408e-984b-9af459934eb0
-- title:
--   Theorem 5.4 — in supermodular games the dynamic (T) is cooperative and irreducible
-- statement:
--   Let $G$ be a strictly supermodular game with at least one strategy per player, and let the shock densities satisfy the conditions of Theorem 2.1. Write $g$ for the field of (T). Then:
--
--   1. (T) is cooperative on $T(\Sigma)$: $\partial g^\alpha_i/\partial v^\beta_j(v) \ge 0$ for all $v \in T(\Sigma)$ and all distinct components $(\alpha,i) \ne (\beta,j)$.
--   2. If two distinct players each have at least two strategies, (T) is irreducible on $T(\Sigma)$: for every nonempty proper set $I$ of components there are $(\alpha,i) \in I$ and $(\beta,j) \notin I$ with $\partial g^\alpha_i/\partial v^\beta_j(v) \ne 0$ for every $v \in T(\Sigma)$.
--
--   Cooperative irreducible systems are strongly monotone, which yields Corollary 5.5.
--
--   **Formalization Note** The proof on p. 31 picks a pair of components belonging to two different players; this needs two distinct players that each have at least two strategies (players with a single strategy own no components and are allowed). When a single player owns all the components and has at least two of them (e.g. strategy counts $(3,1)$), the game is supermodular vacuously while irreducibility fails, so the irreducibility clause carries that assumption explicitly. Irreducibility is in the uniform form the proof establishes (see the Cooperative definition).
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 20, Theorem 5.4 (proof p. 31)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel
import Definitions.Def_StochFictPlay_Supermodular_Game
import Definitions.Def_StochFictPlay_Supermodular_StochOrder
import Definitions.Def_StochFictPlay_Supermodular_Cooperative

open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- Theorem 5.4 (Hofbauer–Sandholm 2002, manuscript p. 20). If `G` is strictly supermodular (and
the shock densities meet the conditions of Theorem 2.1), the dynamic `(T)` on `T(Σ)` is
cooperative: `∂g^α_i/∂v^β_j (v) ≥ 0` for all `v ∈ T(Σ)` and all distinct components
`(α, i) ≠ (β, j)`. It is also irreducible (in the uniform form proved on p. 31: for each nonempty
proper set `I` of components there are `(α, i) ∈ I` and `(β, j) ∉ I` with
`∂g^α_i/∂v^β_j (v) ≠ 0` at every `v ∈ T(Σ)`), provided two distinct players each have at least
two strategies. The proof on p. 31 picks the pair with `α ≠ β`, which needs components of two
different players; when a single player owns all the components and has at least two of them
(e.g. `n = (3, 1)`), the game is supermodular vacuously while irreducibility fails. Players with
a single strategy (no components) are allowed. -/
theorem thm54_cooperative_irreducible {p : ℕ} (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α)) :
    IsCooperative (gField f u) (TSigma n) ∧
      ((∃ α β : Fin p, α ≠ β ∧ 2 ≤ n α ∧ 2 ≤ n β) → IsIrreducible (gField f u) (TSigma n)) := by sorry

end StochFictPlay.Supermodular
