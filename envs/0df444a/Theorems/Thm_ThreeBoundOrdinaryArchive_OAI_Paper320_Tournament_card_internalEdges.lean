-- Prove2me | Theorems.Thm_ThreeBoundOrdinaryArchive_OAI_Paper320_Tournament_card_internalEdges
-- name    : ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.card_internalEdges
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:38:01.44343+00:00
-- url     : https://prove2.me/theorems/a8fc04f3-4178-4091-b543-ff04f889000b
-- title:
--   A tournament has one internal edge per unordered vertex pair
-- statement:
--   Let \(T\) be a tournament on \(\operatorname{Fin}(k)\), and let \(I\) be a finite set of its vertices. If \(E_T(I)\) is the set of directed edges with both endpoints in \(I\), then
--   \[
--   |E_T(I)|=\binom{|I|}{2}.
--   \]
--   This identity supplies the exact edge count in the tournament budget arguments.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, ArchivedOrdinaryCaps, lines 300–326; source SHA256 e5bb0155feceabeb1058dbedb95b06b12a12e94f86ba9b7d02097cc1f2cd8a09.

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
namespace ThreeBoundOrdinaryArchive.SensitivityQ
end ThreeBoundOrdinaryArchive.SensitivityQ
namespace ThreeBoundOrdinaryArchive.ZL
end ThreeBoundOrdinaryArchive.ZL
namespace ThreeBoundOrdinaryArchive.ZP
end ThreeBoundOrdinaryArchive.ZP
open OAI.Paper320
namespace ThreeBoundOrdinaryArchive
end ThreeBoundOrdinaryArchive
open ThreeBoundOrdinaryArchive
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
open OAI.Paper320 Sensitivity205 Sensitivity2075
open scoped Classical BigOperators
namespace ThreeBoundOrdinaryArchive.OAI
end ThreeBoundOrdinaryArchive.OAI
open ThreeBoundOrdinaryArchive.OAI
namespace ThreeBoundOrdinaryArchive.OAI.Paper320
end ThreeBoundOrdinaryArchive.OAI.Paper320
open ThreeBoundOrdinaryArchive.OAI.Paper320
namespace ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament
end ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament
open ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament
variable {k : ℕ} (T : Tournament k)

theorem ThreeBoundOrdinaryArchive.OAI.Paper320.Tournament.card_internalEdges (I : Finset (Fin k)) :
    (T.internalEdges I).card = I.card.choose 2 := by sorry
