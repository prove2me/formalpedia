-- Prove2me | Theorems.Thm_PersistClust_Count_enat_add_sub_cancel_left
-- name    : PersistClust.Count.enat_add_sub_cancel_left
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T10:03:15.620825+00:00
-- url     : https://prove2.me/theorems/24a88626-dce9-42c0-a0da-96ffbee5b9f6
-- title:
--   Extended naturals: (a + b) − a = b for finite first addend (⊤ second allowed)
-- statement:
--   In the extended natural numbers ℕ∞ = ENat, truncated subtraction cancels a finite first addend: for all a b : ℕ∞ with a ≠ ⊤, (a + b) − a = b. The second addend may be ⊤ — in that case a + ⊤ = ⊤ and ⊤ − a = ⊤ (truncated subtraction saturates), which is again b. Proof: case on a: the ⊤ case contradicts hfin; the ↗m case splits on b: if b = ⊤ both sides are ⊤ by the saturation lemmas (simp), and if b = ↗n the arithmetic transports to the naturals by exact_mod_cast of Nat.add_sub_cancel_left m n. This cancellation is the ℕ∞-algebra step that lets rank differences telescope when the minuend is a finite rank (q-tameness supplies finiteness), used throughout the box-combination arithmetic of the matching-census assembly.
-- source:
--   Support theorem of the persistence-clustering deliverable (RR-6968, Theorem 4.6 cluster): the ℕ∞ subtraction algebra (t3_add_sub in the rankKill master, Scratch_rankR1 L893-899, no in-file helpers) — the cancellation consumed by t3_box_arith, t3_ess_pin and every rank-telescoping site of the matching-census assembly.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem enat_add_sub_cancel_left {a b : ℕ∞} (hfin : a ≠ ⊤) : (a + b) - a = b
    := by sorry
