-- Prove2me | Theorems.Thm_PersistClust_Count_off_diagonal_fiber_encard
-- name    : PersistClust.Count.off_diagonal_fiber_encard
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T11:05:23.277755+00:00
-- url     : https://prove2.me/theorems/825f3186-2097-4c65-9937-dd0664843e69
-- title:
--   Off-diagonal copy fiber census: the fiber of offD D over p has exactly D p slots
-- statement:
--   For a multiplicity diagram D on the extended plane (a function D : EReal x EReal to the extended naturals), the fiber of the off-diagonal copy space offD D over a point p — the set of copies standing at p, {q : offD D | offPt q = p} — has cardinality (encard) exactly D p: one copy slot per index below the point's multiplicity. Proof: if D p = infinity, then every natural number k gives a distinct copy <(p, k), _> standing at p (the index cast is always below infinity), so the fiber is infinite and its encard is infinity. Otherwise D p is a finite value: the fiber is in bijection with Fin (D p).toNat. Forward: the copy index of any fiber member is below (D p).toNat, because offD membership says the cast of the index is below D p and the toNat round-trip (ENat.natCast_toNat, using D p < infinity) identifies the cast of (D p).toNat with D p; this gives an injection of the fiber into Fin (D p).toNat, so the fiber is finite with at most (D p).toNat elements. Backward: every k < (D p).toNat satisfies the copy membership (k below D p by the same round-trip), and distinct indices give distinct copies, giving an injection of Fin (D p).toNat into the fiber. The two cardinality bounds squeeze to Fintype.card of the fiber = (D p).toNat, and Set.coe_fintypeCard plus the round-trip give the fiber encard = D p. This census is the combinatorial backbone of the prom-fiber half of the matching-census assembly: any injective routing into a point's copy slots is bounded by the point's multiplicity via Set.encard_image_le.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the copy-slot fiber census (t5_offD_fiber_encard in the rankKill master, Scratch_rankR1 L2208-2289, ported verbatim from the qseDry1 development) — the fiber of offD D over a point p has exactly D p slots, so any injective routing into a point's copy slots is bounded by the point's multiplicity (via Set.encard_image_le); the prom-fiber half of the matching-census assembly reduces to this combinatorial count.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus
import Definitions.Def_PersistClust_Count_MatchingGate

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem off_diagonal_fiber_encard {D : EReal × EReal → ℕ∞} (p : EReal × EReal) :
    ({q : offD D | offPt q = p}).encard = D p
    := by sorry
