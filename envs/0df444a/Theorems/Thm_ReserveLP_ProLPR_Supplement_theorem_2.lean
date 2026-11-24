-- Prove2me | Theorems.Thm_ReserveLP_ProLPR_Supplement_theorem_2
-- name    : ReserveLP.ProLPR.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:07:57.524134+00:00
-- url     : https://prove2.me/theorems/7de108b8-b0af-4c5d-84e4-f32fe641e990
-- title:
--   Theorem 2 — integrality gap, full finite witness and both printed constants
-- statement:
--   There exist finite auction and buyer sets and a data-set $D$ of nonnegative bids, including two auxiliary zero-bid buyers, with an optimal Profile-LP pair $(s,q)$ and strictly positive value $L=\mathrm{LPObj}_D(s)$, such that every nonnegative reserve vector $r$ satisfies
--
--   $$\mathrm{Rev}_D(r)\le0.828L\quad\text{and}\quad\mathrm{Rev}_D(r)\le2(\sqrt2-1)L.$$
--
--   The same finite witnesses satisfy optimality, positivity and both inequalities. The first coefficient is the literal $207/250$ printed on page 8; the second is the exact coefficient of the page-20 restatement. The former is strictly smaller, so it is not replaced by the latter or by a limit. This is the companion integrality-gap target, independent of the proof of Theorem 1.
--
--   **Formalization Note.** The finite limit construction on pages 20–21 does not establish either finite-attainment assertion as printed. This item retains the complete printed open target rather than treating the construction's limiting bound as a proof or refutation. The proof gap and retained finite terms are recorded in MODERATION_NOTES.md. No epsilon relaxation is substituted.
--
--   Differences from the source:
--   - reading: The gap is expressed using optimal values ESP⋆ and LP⋆ → one optimal LP pair with positive LP objective and a bound against every nonnegative reserve vector; reason: the finite construction is nonzero; this excludes vacuous all-zero witnesses and avoids an unbounded or empty real supremum
--   - encoding: arbitrary finite auction and buyer sets → existential cardinalities m,n and types Fin m, Fin n; reason: every finite data-set can be reindexed this way; no size cutoff or fixed number of buyers is imposed
--   - encoding: the source auction and Profile-LP conventions → the immutable published Model, including distinct profile buyers, nonnegative q, a finite sentinel for infinity, and two distinct auxiliary zero buyers; reason: these are the base mission conventions; benchmark reserves are nonnegative and expectations are not needed here
-- source:
--   Derakhshan, Golrezaei, Paes Leme, LP-based Approximation for Personalized Reserve Prices, arXiv:1905.01526v5, pp. 8, 20–21, Theorem 2

import Mathlib
import Definitions.Def_ReserveLP_ProLPR_Model

namespace ReserveLP.ProLPR.Supplement

/-- The complete finite existential claim on p. 8, together with its p. 20 restatement.
The positive LP objective rules out the all-zero instance. -/
theorem theorem_2 :
    ∃ (m n : ℕ) (D : DataSet (Fin m) (Fin n))
      (s : Fin m → Profile (Fin n) → ℝ) (q : Fin n → ℝ → ℝ),
      LPOptimal D s q ∧ 0 < LPObj D s ∧
      ∀ r : Fin n → ℝ, (∀ b, 0 ≤ r b) →
        rev D r ≤ (0.828 : ℝ) * LPObj D s ∧
        rev D r ≤ (2 * (Real.sqrt 2 - 1)) * LPObj D s := by sorry

end ReserveLP.ProLPR.Supplement
