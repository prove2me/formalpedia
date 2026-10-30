-- Prove2me | Theorems.Thm_QseriesFormalization_PartII_Ch07_rogersRamanujan_first_given_step1
-- name    : QseriesFormalization.PartII.Ch07.rogersRamanujan_first_given_step1
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T09:22:34.906625+00:00
-- url     : https://prove2.me/theorems/6deb225f-344b-480c-b207-d8d667ec4455
-- title:
--   First Rogers-Ramanujan identity, conditional on the theta-series Step 1
-- statement:
--   Let $q\in\mathbb{C}$ with $0<|q|<1$ and write $G(q)=J(1,q)=\sum_{n\ge0}q^{n^2}/(q;q)_n$. Assume the hypothesis (Step 1)
--   $$G(q)\cdot\prod_{n\ge1}(1-q^{n})=\sum_{j\in\mathbb{Z}}(-1)^jq^{j(5j+1)/2}.$$
--   Then
--   $$G(q)\cdot\prod_{n\ge0}(1-q^{5n+1})\cdot\prod_{n\ge0}(1-q^{5n+4})=1,$$
--   i.e. $G(q)=1/\big((q;q^5)_\infty(q^4;q^5)_\infty\big)$. The statement is conditional on the Step 1 hypothesis; the unconditional first Rogers-Ramanujan identity is a separate theorem in the same chapter (Chapter 7).
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 7. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Chapter07.lean#L1490-L1545

import Definitions.Def_QseriesFormalization_Chapter07
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Chapter 7 — Part II: Rogers-Ramanujan: first proof (functional equation)

(Hei-Chi Chan, *An Invitation to q-Series*, Ch 7, pp. 47-52.)

Stub: definitions and theorem statements to be filled in as we work
through the chapter.
-/

open QseriesFormalization
open QseriesFormalization.PartII
open QseriesFormalization.PartII.Ch07

variable {R : Type*} [Field R]

/-! ### Theorem 7.3 — The a-deformed Rogers-Ramanujan identity (Chan Eq. 7.4)

The exponent `λ(r) = r(5r+1)/2` (Chan Eq. 7.5) and the function
`C_r(a) = 1 / ((q)_1 (q)_2 ⋯ (q)_r (aq^r)(aq^{r+1})⋯)`
(Chan Eq. 7.6). Theorem 7.3 states:
  `∑_{n≥0} q^{n²+(1-m)n} a^n / (q)_n
     = ∑_{r≥0} (-1)^r a^{2r} q^{λ(r)-mr} (1 - a^m q^{2mr}) C_r(a)`.
Setting `m = 2, a = q` recovers the first Rogers-Ramanujan identity. -/

/-! ### Rogers-Ramanujan functional equation (Chan §7.1)

The generalized Rogers-Ramanujan function is
`J(x, q, N) = ∑_{n=0}^N x^n q^{n²} / (q;q)_n`.

The key functional equation is  `J(x) - J(xq) = xq · J(xq², N-1)`,
which holds termwise because `x^n q^{n²} (1 - q^n) / (q;q)_n`
telescopes via `(1 - q^n) / (q;q)_n = 1 / (q;q)_{n-1}`. -/

/-! The finite functional equation:
`rrJ x q (N+1) - rrJ (x*q) q (N+1) = x*q * rrJ (x*q²) q N`

under appropriate nonvanishing of `(q;q)_n` for `n ≤ N+1`. -/

/-! #### General functional equation by induction

The finite functional equation `J(x, N+1) - J(xq, N+1) = xq · J(xq², N)`
holds for all `N` under nonvanishing of `(q;q)_m` for `m ≤ N+1`. -/

/-! ### Infinite Rogers-Ramanujan series: convergence infrastructure

For complex `q` with `‖q‖ < 1`, the finite q-Pochhammer `(q;q)_n` is nonzero,
and the terms `x^n q^{n²} / (q;q)_n` decay super-exponentially. -/

open scoped Topology
open Filter

/-! ## Rogers-Ramanujan first identity — Step 4 (conditional on Step 1 reduction)

Given the **Step 1** sum-to-theta reduction (proved separately via Schur+Tannery),
we can derive the R-R first/second product form. This conditional theorem makes
the dependency explicit. -/

theorem QseriesFormalization.PartII.Ch07.rogersRamanujan_first_given_step1
    (q : ℂ) (hq : ‖q‖ < 1) (hq_ne : q ≠ 0)
    (h_step1 :
      rrJInf 1 q * PartI.Ch04.eulerPentagonalInfiniteProduct q =
        ∑' j : ℤ, (-1 : ℂ) ^ j * q ^ (j * (5 * j + 1) / 2)) :
    rrJInf 1 q * (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 1 n) *
      (∏' n : ℕ, PartI.Ch04.rrMod5Factor q 4 n) = 1 := by sorry
