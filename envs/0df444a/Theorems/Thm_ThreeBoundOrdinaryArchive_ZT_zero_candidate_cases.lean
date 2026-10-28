-- Prove2me | Theorems.Thm_ThreeBoundOrdinaryArchive_ZT_zero_candidate_cases
-- name    : ThreeBoundOrdinaryArchive.ZT.zero_candidate_cases
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:38:03.373962+00:00
-- url     : https://prove2.me/theorems/17ce1621-bd0d-48d7-83c1-7c7c25fedc3a
-- title:
--   Eight explicit bounds cover the zero-tolerance candidate cases
-- statement:
--   Let \(t,u,m,\delta,z,a,b,s,j,d\) be natural numbers describing the zero-tolerance candidate count, positive-candidate count, guard count, excess charge, total cost, and five child-cost bounds. Assume \(u\le1\), \(m\le3\), \(\binom{u+m}{2}\le m\), \(t\le22\), and \(\delta+um+\binom u2\le m-\binom m2\). Also impose the source bound \(t-u\le19+\delta\) when \(u+m\ge1\), and the double-dominator bound \(t-u\le17+\delta\) when \(u+m\ge2\). If \(z\) satisfies the defined candidate-cost bound and the additional shared-head bound when \(u=m=1\), then
--   \[
--   z\le\max\{22b,\ a+19b,\ 17b+\max(\min(a+s,d),a+j),\
--   19b+s,\ 20b+j,\ 17b+s+j,\ 18b+2j,\ 17b+3j\}.
--   \]
--   This finite arithmetic reduction supplies the zero-tolerance transfer expression.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ArchivedOrdinaryZero, lines 627–684; source SHA256 3d50b311c7ac8a52a9f924c89576c84e7131724e045e1bccdd469a1d32c2b4dd.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Sensitivity213303_ArchivedOrdinaryDefinitions

namespace OAI.Paper320
end OAI.Paper320
namespace ThreeBoundOrdinaryArchive.OAI.Paper320
end ThreeBoundOrdinaryArchive.OAI.Paper320
namespace ThreeBoundOrdinaryArchive.Sensitivity205
end ThreeBoundOrdinaryArchive.Sensitivity205
namespace ThreeBoundOrdinaryArchive.Sensitivity2075
end ThreeBoundOrdinaryArchive.Sensitivity2075
namespace ThreeBoundOrdinaryArchive.SensitivityOrdinaryGuard
end ThreeBoundOrdinaryArchive.SensitivityOrdinaryGuard
namespace ThreeBoundOrdinaryArchive.SensitivityQ
end ThreeBoundOrdinaryArchive.SensitivityQ
namespace ThreeBoundOrdinaryArchive.SensitivitySourceZero
end ThreeBoundOrdinaryArchive.SensitivitySourceZero
namespace ThreeBoundOrdinaryArchive.ZL
end ThreeBoundOrdinaryArchive.ZL
open OAI.Paper320
namespace ThreeBoundOrdinaryArchive
end ThreeBoundOrdinaryArchive
open ThreeBoundOrdinaryArchive
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace ThreeBoundOrdinaryArchive.ZT
end ThreeBoundOrdinaryArchive.ZT
open ThreeBoundOrdinaryArchive.ZT

theorem ThreeBoundOrdinaryArchive.ZT.zero_candidate_cases (z t u m δ a b s j d : ℕ)
    (hu : u ≤ 1) (hm : m ≤ 3) (hc : (u+m).choose 2 ≤ m)
    (ht : t ≤ 22)
    (hδ : δ+((u*m+u.choose 2)-0*u) ≤ m*(0+1)-m.choose 2)
    (hsource : 1 ≤ u+m → t-u ≤ 19+δ)
    (hdouble : 2 ≤ u+m → t-u ≤ 17+δ)
    (hraw : z ≤ candidateCost 0 t u m δ a b s j)
    (hshared : u=1 → m=1 → z ≤ (t-1)*b+max (min (a+s) d) (a+j)) :
    z ≤ zeroCost a b s j d := by sorry
