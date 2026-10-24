-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_Ch13RRCF_rrcf_r_mul_pentagonal023SeriesPS_eq
-- name    : QseriesFormalization.Pending.Ch13RRCF.rrcf_r_mul_pentagonal023SeriesPS_eq
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-23T11:08:54.777255+00:00
-- url     : https://prove2.me/theorems/7883c2b5-9f12-4d31-9385-c2688382bd5b
-- title:
--   Multiplicative form: $r(q)\,(q^2,q^3,q^5;q^5)_\infty=(q,q^4,q^5;q^5)_\infty$
-- statement:
--   In $\mathbb{Q}[[X]]$, with $r=P_{014}P_{023}^{-1}$ the Rogers--Ramanujan quotient series, $$r\cdot P_{023}=P_{014},$$ where $P_{014}=\sum(-1)^kX^{k(5k-3)/2}$ and $P_{023}=\sum(-1)^kX^{k(5k-1)/2}$ are the formal pentagonal series for $(q,q^4,q^5;q^5)_\infty$ and $(q^2,q^3,q^5;q^5)_\infty$. This is the defining relation of $r$ in Chapter 13.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011), Chapter 13. Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/Chapter13_RRCF_RForm.lean#L110-L123

import Definitions.Def_QseriesFormalization_Pending_Chapter13_RRCF_RForm
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith

namespace QseriesFormalization.Pending.Ch16MBIProof end QseriesFormalization.Pending.Ch16MBIProof

/-!
# Chapter 13 / §11.5 — the Rogers–Ramanujan continued fraction in fractional-power-free form

Chan's "difficult and deep" identity (Theorem 11.5) relates `u = R(q)` and `v = R(q⁵)`:
`u⁵ = v · (1 − 2v + 4v² − 3v³ + v⁴) / (1 + 3v + 4v² + 2v³ + v⁴)`.

The repo's `Chapter11.R_trunc` is a DEGENERATE truncation (its recurrence
`R_{n+1} = 1/(1+q^{n+1}R_n)` has `q^{n+1}→0`, so it converges trivially to `1`, NOT to the RRCF).
This file builds the CORRECT, fractional-power-free object.

**Key device.** `R(q) = q^{1/5}·r(q)` where
`r(q) = (q;q⁵)∞(q⁴;q⁵)∞ / ((q²;q⁵)∞(q³;q⁵)∞)` has NO fractional power — it is a genuine formal
power series. Moreover `r(q) = H(q)/G(q)` where `G,H` are the two Rogers–Ramanujan products; in the
repo's keystone variables `r = pentagonal014SeriesPS / pentagonal023SeriesPS` (numerically confirmed:
`pentagonal014 = (q,q⁴,q⁵;q⁵)`, `pentagonal023 = (q²,q³,q⁵;q⁵)`, and the `(q⁵;q⁵)` factors cancel in the
ratio, leaving exactly `r`).

With `u = q^{1/5} r(q)`, `v = q·r(q⁵)` (note `(q⁵)^{1/5} = q`, so `v` is fractional-power-free too),
Theorem 11.5 becomes the FORMAL POWER SERIES identity (verified numerically to degree 60, residual 0):
```
r(q)⁵ · (1 + 3v + 4v² + 2v³ + v⁴)  =  r(q⁵) · (1 − 2v + 4v² − 3v³ + v⁴),    v := X · r(q⁵).
```
`r(q⁵) = PowerSeries.expand 5 r`.

**Proof strategy (next steps, deep — Hardy: "difficult and deep").** This `u⁵ = v·N(v)/D(v)` form is
NOT the same as the R(q)-only quintic already proved in `RamanujanQuinticJTP` (`core·E(q⁵)=E(q)¹¹`); it
ADDITIONALLY relates `R(q)` to `R(q⁵)`, and the standard route is the **Gugg telescoping** (Chan §13.1 /
Hirschhorn §9.2): a product `Q = ∏ₖ tₖ` of single-mode factors telescopes to `R(q)⁵/R(q⁵)`, while a
second evaluation gives the rational function in `R(q⁵)`. Formalizing that telescoping is the substantial
remaining work. This file lays the fractional-power-free foundation only.
-/

open QseriesFormalization
open QseriesFormalization.Pending
open QseriesFormalization.Pending.Ch13RRCF

open QseriesFormalization.Pending.JTPFormalPSPentagonal

/-! ## Well-definedness of `rrcf_r`

Section 13.1 of Chan (and §9.2 of Hirschhorn) treats `r(q)` as if it were a
genuine power series; that is justified here because the denominator
`pentagonal023SeriesPS ℚ` has constant term `1`, hence is a unit in `ℚ⟦X⟧`,
hence has the standard formal-PS inverse and `rrcf_r · pentagonal023 =
pentagonal014` as a formal equality.  None of this is the deep Chan §13
identity (that requires Gugg telescoping); these are the bookkeeping facts
that need to be in place before any closure attempt can begin.
-/

open QseriesFormalization.Pending.JTPFormalPSPentagonal
open QseriesFormalization.Pending.Ch16MBIProof

theorem QseriesFormalization.Pending.Ch13RRCF.rrcf_r_mul_pentagonal023SeriesPS_eq :
    rrcf_r * pentagonal023SeriesPS ℚ = pentagonal014SeriesPS ℚ := by sorry
