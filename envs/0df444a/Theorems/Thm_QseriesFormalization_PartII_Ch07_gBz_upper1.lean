-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_gBz_upper1
-- name    : QseriesFormalization.PartII.Ch07.gBz_upper1
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:20:22.005563+00:00
-- url     : https://prove2.me/theorems/a7c85ab3-16c0-4591-91c9-ecdab2974591
-- title:
--   Upper $q$-Pascal rule for the zero-extended Gaussian binomial
-- statement:
--   Let $q\in\mathbb{C}$, $n\in\mathbb{N}$, $k\in\mathbb{Z}$, and let $[n,k]_q$ be the Gaussian binomial coefficient extended by zero outside $0\le k\le n$ (`gBz`). Then
--   $$[n+1,k]_q=q^{\max(k,0)}\,[n,k]_q+[n,k-1]_q,$$
--   with the exponent being the natural-number truncation of $k$. This is the second Pascal rule, valid for all integers $k$, used in Chapter 7.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep1.lean#L558-L584

import Definitions.Def_QseriesFormalization_Chapter07_RRStep1
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 7 — Rogers-Ramanujan Step 1 (Schur finite identity + Tannery)

Isolated module for the deepest R-R step: the Schur polynomial recurrence,
its identification with the finite Gaussian sum, and the Tannery limit
yielding `rrJInf 1 q · (q;q)_∞ = ∑'_j (-1)^j q^(j(5j+1)/2)`.

See `docs/RR_step1_schur.md`.
-/

open QseriesFormalization
open QseriesFormalization.PartII
open QseriesFormalization.PartII.Ch07

open Filter Topology

/-! ### Schur recurrence for `schurSum`

The crux of Step 1: `schurSum q (N+2) = schurSum q (N+1) + q^(N+1)·schurSum q N`.

Proof (verified by hand, exponent algebra):

`S q (N+2) = ∑_n q^(n²)·[N+2-n choose n]_q`. Apply gaussianBinom Pascal
(`[m+1 choose k+1]_q = [m choose k+1]_q + q^(m-k)·[m choose k]_q` with
`m=N+1-n, k=n-1`):

`[N+2-n choose n]_q = [N+1-n choose n]_q + q^(N+2-2n)·[N+1-n choose n-1]_q`

So `S q (N+2) = S q (N+1) + ∑_n q^(n²+N+2-2n)·[N+1-n choose n-1]_q`.
Reindex `n = m+1`: `q^((m+1)²+N+2-2(m+1)) = q^(m²+N+1)`, and
`[N+1-(m+1) choose m]_q = [N-m choose m]_q`. So the second sum
`= q^(N+1)·∑_m q^(m²)·[N-m choose m]_q = q^(N+1)·S q N`. ∎

The Lean formalization of this Finset reindex + Pascal split is in
`schurSum_recurrence` (below), and `rrPoly_eq_schurSum` follows by
two-step induction. -/

/-! ### Tannery LHS — pointwise gaussianBinom limit -/

/-! ### Schur RHS — parity-split theta-Gaussian finite sum (FORM UNRESOLVED)

**Sanity-check failure (2026-05-15)**: the naively-stated Schur RHS form

`d_{2M} = ∑_{j=-M}^{M} (-1)^j q^(j(5j+1)/2) [2M choose M-j]_q`

does NOT satisfy `d_2 = 1 + q`. Direct computation at `M=1` (j ∈ {-1,0,1}):
`(-1)·q²·[2,2] + 1·q⁰·[2,1] + (-1)·q³·[2,0] = -q² + (1+q) - q³`,
which is `1+q-q²-q³ ≠ 1+q = rrPoly q 2 = schurSum q 2` (both proven above).

So a convention is off: the bottom index is likely `⌊(N-5j)/2⌋` (with `5j`,
not `2j`), OR the polynomial is the H-type `∑ q^(n²+n)[…]`, OR the exponent
differs. This requires a careful literature reference (Andrews,
*The Theory of Partitions*, Thm 7.x; or Sills, *An Invitation to the
Rogers–Ramanujan Identities*) and must NOT be guessed.

**Generalized pentagonal helper** (correct & reusable regardless of the
final bottom-index convention): -/

/-! ### Schur recurrence via carry-telescope (ChatGPT extended-pro skeleton) -/

/-! #### Unconditional single-step q-Pascal (via gBz zero-extension) -/

theorem QseriesFormalization.PartII.Ch07.gBz_upper1 (q : ℂ) (n : ℕ) (k : ℤ) :
    gBz q (n + 1) k = q ^ k.toNat * gBz q n k + gBz q n (k - 1) := by sorry
