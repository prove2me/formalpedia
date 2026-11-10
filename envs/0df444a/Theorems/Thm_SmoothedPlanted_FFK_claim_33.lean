-- Prove2me | Theorems.Thm_SmoothedPlanted_FFK_claim_33
-- name    : SmoothedPlanted.FFK.claim_33
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:33:39.556775+00:00
-- url     : https://prove2.me/theorems/05baa0a9-2fe3-44c5-8c86-cc6bdd83b719
-- title:
--   Claim 33 — planted assignment is ∆-consistent iff its literal set spans ⩽ ∆ edges of H
-- statement:
--   For any pairwise CSP instance $Y$, set $S$, assignment $\sigma:S\to[q]$ and real budget $\Delta$, let $I_\sigma=\{(i,\sigma_i):i\in S\}$. Then
--   $$\sigma\text{ is }\Delta\text{-consistent}\quad\Longleftrightarrow\quad |E(H[I_\sigma])|\le\Delta.$$
--   This identifies CSP violations with edges spanned by the assignment's literal set.
--
--   Differences from the source:
--   - encoding: finite variables and alphabet → variables and alphabet indexed by Fin n and Fin q; unordered pairs represented by i < j; reason: finite relabelling is bijective and counts every pair once
--   - generalization: labels y of a fixed CSP type, with symmetric relations R_y → all symmetric Boolean relations are available as labels; reason: pushforward along y ↦ R_y preserves every constraint and violation probability; each original type is a subclass
--   - generalization: nonnegative violation budgets when used for recovery → the equivalence is stated for every real Δ; reason: both sides are the same nonnegative count comparison, including when Δ is negative
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Claim 33, printed p. 23 (PDF p. 25), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Consistent
import Definitions.Def_SmoothedPlanted_FFK_Incompatibility

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

theorem claim_33 {n q : ℕ} (Y : CSP (Fin n) q) (S : Finset (Fin n))
    (σ : S → Fin q) (Δ : ℝ) :
    Consistent Y S σ Δ ↔
      (spannedEdges (incompatibility Y) (literalSet S σ) : ℝ) ≤ Δ := by sorry

end SmoothedPlanted.FFK
