-- Prove2me | Theorems.Thm_QseriesFormalization_Pending_SignMod3_jacobiTripleSign_mod3
-- name    : QseriesFormalization.Pending.SignMod3.jacobiTripleSign_mod3
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-23T14:50:33.51124+00:00
-- url     : https://prove2.me/theorems/95b4c72b-47c1-493c-86d4-90c310483edd
-- title:
--   Jacobi triple sign mod $3$ is the pentagonal sign stretched by $3$
-- statement:
--   For every $n\in\mathbb{N}$, in $\mathbb{Z}/3$, $$\tau(n)\equiv\begin{cases}\sigma(n/3)&3\mid n,\\0&\text{otherwise,}\end{cases}$$ where $\tau(m)=(-1)^k(2k+1)$ if $m=k(k+1)/2$ ($0$ otherwise) is the Jacobi triple sign and $\sigma(m)=(-1)^k$ if $m=k(3k\mp1)/2$ ($0$ otherwise) is the pentagonal sign. Equivalent to $(q;q)_\infty^3\equiv(q^3;q^3)_\infty\pmod 3$ at the level of coefficients.
-- source:
--   Lean formalization (Xiang Huang) of Hei-Chi Chan, An Invitation to q-Series: From Jacobi's Triple Product Identity to Ramanujan's "Most Beautiful Identity" (World Scientific, 2011). Lean source: https://github.com/xiangyazi24/invitation-to-qseries-lean/blob/5df34b280b6a9c4a68ab09105b4e5d3c7bbe88d1/QseriesFormalization/Pending/SignSequences_Mod3.lean#L33-L45

import Definitions.Def_QseriesFormalization_Chapter05_Franklin
import Definitions.Def_QseriesFormalization_DefCoreQSeries
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# A mod-3 identity between the two fundamental sign sequences

Over `ZMod 3`, the Jacobi-triple-sign sequence (coefficients of `(q;q)_∞^3`) is the
pentagonal-sign sequence (coefficients of `(q;q)_∞`) stretched by a factor of 3:

  `jacobiTripleSign n ≡ [3 ∣ n] · pentagonalSign (n/3)   (mod 3).`

Proof: B2 gives `(qPoch)^3 = jacobiThetaPS`, and the char-3 Frobenius gives
`(qPoch)^3 = expand 3 qPoch` over `ZMod 3`.  Hence `jacobiThetaPS (ZMod 3) =
expand 3 (qPochInfPS (ZMod 3))`, and reading off coefficients (with
`coeff_qPochInfPS_eq_pentagonalSign`) yields the claim.
-/

open QseriesFormalization

open PowerSeries
open QseriesFormalization.PartIV.Ch19

theorem QseriesFormalization.Pending.SignMod3.jacobiTripleSign_mod3 (n : ℕ) :
    ((jacobiTripleSign n : ℤ) : ZMod 3) =
      if 3 ∣ n then ((QseriesFormalization.PartI.Ch04Franklin.pentagonalSign (n / 3) : ℤ) : ZMod 3)
      else 0 := by sorry
