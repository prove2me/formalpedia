-- Prove2me | Theorems.Thm_StochFictPlay_Supermodular_thm54_cooperative_irreducible_v2
-- name    : StochFictPlay.Supermodular.thm54_cooperative_irreducible_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:42:27.337464+00:00
-- url     : https://prove2.me/theorems/8443c20b-ccd6-4a2b-a037-8ed814ede348
-- title:
--   Theorem 5.4 — in supermodular games with continuous strictly positive shock densities the dynamic (T) is cooperative and irreducible
-- statement:
--   Let $G$ be a strictly supermodular game with at least one strategy per player, and let each player's shock density satisfy the conditions of Theorem 2.1 — a continuous, finite, everywhere strictly positive probability density whose choice function is continuously differentiable. Write $g$ for the field of (T). Then:
--
--   1. (T) is cooperative on $T(\Sigma)$: $\partial g^\alpha_i/\partial v^\beta_j(v) \ge 0$ for all $v \in T(\Sigma)$ and all distinct components $(\alpha,i) \ne (\beta,j)$.
--   2. If two distinct players each have at least two strategies, (T) is irreducible on $T(\Sigma)$: for every nonempty proper set $I$ of components there are $(\alpha,i) \in I$ and $(\beta,j) \notin I$ with $\partial g^\alpha_i/\partial v^\beta_j(v) \ne 0$ for every $v \in T(\Sigma)$.
--
--   Cooperative irreducible systems are strongly monotone, which yields Corollary 5.5.
--
--   **Formalization Note.** The retired version imported a definition of "strictly positive density" asking only for pointwise positivity of one measurable representative; a density whose continuous version vanishes on the tie hyperplane passed it after a null-set patch, and the off-diagonal partial $\partial \hat B^\alpha_i/\partial v^\beta_j$, which the proof on p. 31 shows is $> 0$, vanished at the tie point, so irreducibility failed. The new statement is textually the same over the corrected definition chain (ChoiceModel, Game, StochOrder, Cooperative re-issued as `_v2`), in which each shock density is a continuous, finite, strictly positive representative — the version the paper's eq. (4) integrates over hyperplanes, which makes the partials in (17) strictly positive and hence the off-diagonal partials of (T) across players strictly positive. Conventions made explicit: the paper's "supermodular" is defined on pp. 18–19 with *strictly* increasing differences, which is the hypothesis used; the proof on p. 31 picks a pair of components belonging to two different players, which needs two distinct players that each have at least two strategies (players with a single strategy own no components and are allowed) — when a single player owns all components (e.g. strategy counts $(3,1)$) the game is supermodular vacuously while irreducibility fails, so the irreducibility clause carries that assumption explicitly; irreducibility is in the uniform form the proof establishes; partial derivatives are entries of the Fréchet derivative of the field, which is $C^1$ under the hypotheses.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 20, Theorem 5.4 (proof p. 31), with the shock densities satisfying the hypotheses of Theorem 2.1 (p. 5) read with the regularity used in eq. (4) (p. 6)

import Mathlib
import Definitions.Def_StochFictPlay_Supermodular_ChoiceModel_v2
import Definitions.Def_StochFictPlay_Supermodular_Game_v2
import Definitions.Def_StochFictPlay_Supermodular_StochOrder_v2
import Definitions.Def_StochFictPlay_Supermodular_Cooperative_v2

open scoped ENNReal

namespace StochFictPlay.Supermodular

/-- Theorem 5.4 (Hofbauer–Sandholm 2002, manuscript p. 20). If `G` is strictly supermodular (and
the shock densities meet the conditions of Theorem 2.1 — `IsRegularDensity`: continuous,
everywhere finite, strictly positive probability densities with `C¹` choice functions), the
dynamic `(T)` on `T(Σ)` is cooperative: `∂g^α_i/∂v^β_j (v) ≥ 0` for all `v ∈ T(Σ)` and all
distinct components `(α, i) ≠ (β, j)`. It is also irreducible (in the uniform form proved on
p. 31: for each nonempty proper set `I` of components there are `(α, i) ∈ I` and `(β, j) ∉ I`
with `∂g^α_i/∂v^β_j (v) ≠ 0` at every `v ∈ T(Σ)`), provided two distinct players each have at
least two strategies. The proof on p. 31 picks the pair with `α ≠ β`, which needs components of
two different players; when a single player owns all the components and has at least two of
them (e.g. `n = (3, 1)`), the game is supermodular vacuously while irreducibility fails. Players
with a single strategy (no components) are allowed.

Corrected version of `thm54_cooperative_irreducible`, which imported a definition of
`IsRegularDensity` asking only for pointwise positivity of one measurable version of the density;
a density whose continuous version vanishes on the tie hyperplane was patched on a null set to
pass it, and the off-diagonal partial `∂B̂^α_i/∂v^β_j`, which the proof shows is `> 0`, vanished at
the tie point, so irreducibility failed. The statement is unchanged; the fix is in the imported
definition modules (re-issued as `_v2`). -/
theorem thm54_cooperative_irreducible_v2 {p : ℕ} (n : Fin p → ℕ) (hn : ∀ α, 1 ≤ n α)
    (u : (α : Fin p) → Profile n → ℝ) (hu : IsStrictlySupermodular u)
    (f : (α : Fin p) → (Fin (n α) → ℝ) → ℝ≥0∞) (hf : ∀ α, IsRegularDensity (f α)) :
    IsCooperative (gField f u) (TSigma n) ∧
      ((∃ α β : Fin p, α ≠ β ∧ 2 ≤ n α ∧ 2 ≤ n β) → IsIrreducible (gField f u) (TSigma n)) := by sorry

end StochFictPlay.Supermodular
