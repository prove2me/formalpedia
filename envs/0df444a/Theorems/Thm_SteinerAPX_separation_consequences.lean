-- Prove2me | Theorems.Thm_SteinerAPX_separation_consequences
-- name    : SteinerAPX.separation_consequences
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:37:20.685374+00:00
-- url     : https://prove2.me/theorems/0e99b709-7343-48a1-9e2a-39939fbcfea6
-- title:
--   §4.1, p.14 — consequences of separation: distinct cables are $\ge\frac43$ apart, at most $L$ segments, $|U|<L$
-- statement:
--   Let $H$ be a 3DM-3 instance and consider a well-formed, separated cable layout of $H$ in $\mathbb R^D$ with total cable length $L$. Then:
--
--   1. the radial segments leaving two distinct ports of a gadget (in orthogonal or opposite directions) are at least $\frac43$ apart;
--   2. any two points on different cables are at least $\frac43$ apart;
--   3. the number of cable segments is at most $L$;
--   4. $|U|=3r<L$.
--
--   These facts are used throughout the cable reduction: the separation of cables bounds how attachments of a connector can be grouped, and $|U|<L$ absorbs error terms of order $\rho|U|$ into $O(\rho L)$.
--
--   Differences from the source:
--   - generalization: b₁, b₂ two orthogonal unit coordinate vectors of ℝᴰ → b₁, b₂ any orthonormal pair (CableLayout.WellFormed) in any EuclideanSpace ℝ ι; reason: a linear isometry of ℝᴰ maps any orthonormal pair onto two coordinate vectors and preserves every quantity in the statement, so the statement specializes to the source's coordinate vectors
--   - encoding: |U| < L for the matching instance H → |U| = 3r < L with r ≥ 1 (built into the instance type); reason: at r = 0 both sides can vanish; r ≥ 1 excludes only the empty instance
-- source:
--   S. Bartlmae, Inapproximability of Euclidean Steiner Tree, STOC 2027 submission (manuscript sha256 6f78a9ea…), §4.1, p.14 (PDF p.16), paragraph after Definition 6

import Mathlib
import Definitions.Def_SteinerAPX_Separated

namespace SteinerAPX

open Inst3DM CableLayout

/-- **Consequences of separation.** S. Bartlmae, *Inapproximability of Euclidean Steiner Tree*,
STOC 2027 submission (manuscript sha256 6f78a9ea…), §4.1, p.14 (PDF p.16): "The segments leaving
distinct ports of a gadget extend in orthogonal or opposite directions and are therefore at least
4/3 apart. Together with (S1), this shows that points on different cables are at least 4/3 apart.
By (S2), there are at most L cable segments, and by (S1), |U| < L."

For a well-formed, separated layout of a 3DM-3 instance `H` in `ℝᴰ`: (1) the radial segments of two
distinct ports of one gadget are at least `4/3` apart; (2) points on different cables are at least
`4/3` apart; (3) the number of cable segments is at most the total cable length `L`; (4)
`|U| = 3r < L`.

**Formalization Note** `r ≥ 1` is part of `Inst3DM`; at `r = 0` both sides of (4) can vanish. -/
theorem separation_consequences {ι : Type} [Fintype ι] (H : Inst3DM)
    (L : CableLayout H (EuclideanSpace ℝ ι)) (hH : H.IsThreeDM3) (hL : L.WellFormed)
    (hsep : Separated L) :
    (∀ s : Gadget H, ∀ i ∈ labels H s, ∀ j ∈ labels H s, i ≠ j →
      ∀ x ∈ L.radial s i, ∀ y ∈ L.radial s j, 4 / 3 ≤ dist x y) ∧
    (∀ i j : Label H, i ≠ j → ∀ x ∈ carrier (L.cable i), ∀ y ∈ carrier (L.cable j),
      4 / 3 ≤ dist x y) ∧
    (((∑ i : Label H, (L.cable i).card : ℕ) : ℝ) ≤ L.totalLen) ∧
    (3 * (H.r : ℝ) < L.totalLen) := by sorry

end SteinerAPX
