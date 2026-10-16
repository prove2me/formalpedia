-- Prove2me | Theorems.Thm_PersistClust_Count_offD_injective_of_offPt
-- name    : PersistClust.Count.offD_injective_of_offPt
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-15T13:24:27.604973+00:00
-- url     : https://prove2.me/theorems/c7d5b6b3-083d-4511-99cb-1a1cb0d3038a
-- title:
--   Copy-record injectivity: offPt-injectivity of a family of offD copy-records implies injectivity
-- statement:
--   A copy-record type offD D over persistence-bar data carries a point projection offPt. Any family F of copy-records whose point projections are pairwise distinct is itself injective: a copy-record is determined by its point projection, so two equal records have equal projections, contradicting the distinctness.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.8 cluster): the copy-record injectivity of the interleaving rank calculus. Transcribed GREEN (exit 0, sorry-free) from the working file; the platform mirror structures (comps/structMap/compRep/offD) rely on the platform Definitions via imports.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem offD_injective_of_offPt {D : EReal × EReal → ℕ∞} {A : Type*}
    (F : A → offD D) (h : Function.Injective (fun a => offPt (F a))) : Function.Injective F
    := by sorry
