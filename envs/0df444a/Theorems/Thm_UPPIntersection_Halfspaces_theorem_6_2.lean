-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_theorem_6_2
-- name    : UPPIntersection.Halfspaces.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:57.284607+00:00
-- url     : https://prove2.me/theorems/1c5ec9f7-ebb8-45cb-80f3-4035092a368c
-- title:
--   Theorem 6.2 — Forster: sign rank is at least the inverse average margin
-- statement:
--   Let $A$ be a sign matrix with finite row set $\mathcal A$ and finite column set $\mathcal B$, and let $\mu$ be a probability distribution on $\mathcal B$. Then
--   $$\operatorname{rank}_\pm(A)\ge\frac1{m^{\mathrm{avg}}_\mu(A)},$$
--   where $\operatorname{rank}_\pm(A)$ is the least rank of a real matrix $R$ with $A_{ab}R_{ab}>0$ for all entries, and $m^{\mathrm{avg}}_\mu(A)$ is the supremum, over all dimensions $r$ and all unit vectors $u_a,v_b\in\mathbb R^r$ with $A_{ab}\langle u_a,v_b\rangle>0$, of $\min_a\mathbb E_{b\sim\mu}|\langle u_a,v_b\rangle|$.
--
--   This is the standard bridge from margin upper bounds to sign-rank lower bounds; Theorem 6.3 extends it to measurable continuous arrangements.
--
--   Differences from the source:
--   - encoding: sign values in {−1, 1}, with −1 meaning logical true → Bool entries with true standing for +1 (as in the published SignRankMargin sign-rank definition); reason: a relabelling of the two values; the signed AND (−1 iff both are −1) becomes Boolean OR of the stored bits, and sign representation becomes A·R > 0 entrywise
--   - encoding: a distribution μ on B → weights μ : B → ℝ with μ ≥ 0 and ∑ μ = 1; reason: finite distributions
--   - encoding: min over the rows a ∈ A (undefined for an empty row set) → real iInf over a finite row type, which is 0 for an empty type, so then the average margin is 0 and 1/0 = 0 makes the inequality trivially true; reason: Lean junk value on a case the source does not define; for every nonempty row set the statement is the source's (the column set is nonempty because ∑ μ = 1)
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 27, Theorem 6.2 (Forster [For02]) with Definition 6.1; PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_UPPIntersection_Halfspaces_SignMatrices

open SignRankMargin.OREquality

namespace UPPIntersection.Halfspaces

theorem theorem_6_2 {X Y : Type} [Fintype X] [Fintype Y]
    (A : Matrix X Y Bool) (μ : Y → ℝ) (hμ0 : ∀ b, 0 ≤ μ b) (hμ1 : ∑ b, μ b = 1) :
    1 / avgMargin A μ ≤ (signRank A : ℝ) := by sorry

end UPPIntersection.Halfspaces
