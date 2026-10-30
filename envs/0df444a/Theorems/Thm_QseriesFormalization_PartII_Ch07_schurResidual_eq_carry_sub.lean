-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_schurResidual_eq_carry_sub
-- name    : QseriesFormalization.PartII.Ch07.schurResidual_eq_carry_sub
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:23:46.330357+00:00
-- url     : https://prove2.me/theorems/99f0a9cd-a39e-4e86-9f1a-03d5e1c63f9c
-- title:
--   Schur residual as a telescoping difference of carries
-- statement:
--   For $q\in\mathbb{C}$, $N\in\mathbb{N}$ and $j\in\mathbb{Z}$, let $\mathrm{residual}(j)=t_{N+2}(j)-t_{N+1}(j)-q^{N+1}t_N(j)$, where $t_n(j)$ is the $j$-th summand of the Schur theta-Gaussian finite sum $\sum_j(-1)^jq^{j(5j+1)/2}\binom{n}{\lfloor(n-5j)/2\rfloor}_q$. Let $\mathrm{carry}(j)$ be the explicit term (nonzero only when $N-5j$ is even) built from a zero-extended Gaussian binomial. Then
--   $$\mathrm{residual}(j)=\mathrm{carry}(j)-\mathrm{carry}(j+1).$$
--   Summing over $j$ shows that the residuals telescope, proving the Schur recurrence in Chapter 7.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07_RRStep1.lean#L673-L721

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

/-! #### Local q-binomial residual identities (Schur 1917 combinatorial core)

Two-Pascal-step cancellation: `gBz(N+2)(b+1)` reduced via one upper and one
lower single-step q-Pascal, with the cross term killed because either the
`toNat` exponents sum to `N+1` (when `0 ≤ b ≤ N`) or `gBz q N b = 0`. -/

/-! #### Carry-telescope proof of the Schur recurrence (unconditional) -/

theorem QseriesFormalization.PartII.Ch07.schurResidual_eq_carry_sub (q : ℂ) (N : ℕ) (j : ℤ) :
    schurResidual q N j = schurCarry q N j - schurCarry q N (j + 1) := by sorry
