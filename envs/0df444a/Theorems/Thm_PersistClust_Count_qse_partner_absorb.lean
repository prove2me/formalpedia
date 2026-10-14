-- Prove2me | Theorems.Thm_PersistClust_Count_qse_partner_absorb
-- name    : PersistClust.Count.qse_partner_absorb
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T05:33:47.285645+00:00
-- url     : https://prove2.me/theorems/472437aa-f4c5-4d85-9776-75f040702bd8
-- title:
--   QSE partner absorb: the dichotomy right-branch output yields the partner bar via the census absorb
-- statement:
--   Let stageY be a cluster filtration over levels ℝ with relation field JY satisfying the FiltrationLaw and IsTameModule tameness, with component classes comps stageY JY t, coarsening maps structMap, birth-sup birthSup, rank function rankFn stageY JY and persistence-diagram multiplicity mult. Fix a window with bottom aw ≤ α − 1 and top (α + ε) − ε, a cell J at the window top with birth-sup e (so α < e and e lies in the ε-band around b: b − ε ≤ e ≤ b + ε), and a boundary level v in the window (aw ≤ v ≤ top). Assume the dichotomy right-branch output: above v, at every level ξ with v < ξ ≤ top the descent of J has birth-sup exactly e (hAbove); strictly between aw and v the descent of J never has birth-sup e (hBelow); and if v sits at the window bottom, the descent of J at aw does not have birth-sup e (hbot). Conclusion: there is a partner level m ≤ α such that b and e are ε-close (closeE b e ε: |b − e| ≤ ε in the EReal ordering) and the diagram records a bar at (e, m): mult (rankFn stageY JY) ((e : EReal), m) ≠ 0. The partner level is v itself (m = (v : EReal) ≤ α since v ≤ (α + ε) − ε = α); the ε-closeness is the band hypothesis. The multiplicity is forced by the census absorb at (e, v) in three window cases: (i) v at the window top — the stable-gap package around (e, v) applies and the thread hypothesis for the absorb is witnessed by the alive-up lift: for every probe η in the gap there is a level-(v+η) cell with birth-sup e (hAbove, since v + η ≤ top), whose descent to v − η does not have birth-sup e (hBelow); the absorb then yields a nonzero count. (ii) v at the window bottom — hbot gives the thread's below-value difference at aw, and descent monotonicity of birth-sups (birth-sups only grow under descent) turns the top thread into the required shape. (iii) v interior — the same absorb with the window-fitted gap, using hAbove above and hBelow below. In each case the census absorb concludes mult (rankFn stageY JY) ((e : EReal), (v : EReal)) ≠ 0.
-- source:
--   T5c Route A absorb (design §8.16.9) of the persistence-clustering deliverable (RR-6968): the factored partner absorb — the strengthened dichotomy's right-branch output at any window bottom aw ≤ α − 1 feeds the census absorb at (e, v) in three window cases, yielding the partner bar (t5_partnerAbsorb in the rankKill master, Scratch_rankR1 L6886-L6994); consumed by the QSE partner-high band (qse_partner_high_band) for the primary window aw = α − 1 and the below-probe re-run in the full-ray case.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem qse_partner_absorb {ιY : Type*} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawY : FiltrationLaw stageY JY) (hTameY : IsTameModule stageY JY)
    {α ε b e aw v : ℝ} {J : comps stageY JY ((α + ε) - ε)}
    (heα : α < e) (hband_lo : b - ε ≤ e) (hband_hi : e ≤ b + ε)
    (haw : aw ≤ α - 1) (hvlo : aw ≤ v) (hvhi : v ≤ (α + ε) - ε)
    (hAbove : ∀ (ξ : ℝ) (hξ : ξ ≤ (α + ε) - ε), v < ξ →
      birthSup hLawY ξ (structMap hLawY hξ J) = e)
    (hBelow : ∀ (ξ : ℝ) (hξ : ξ ≤ (α + ε) - ε), aw ≤ ξ → ξ < v →
      birthSup hLawY ξ (structMap hLawY hξ J) ≠ e)
    (hbot : ∀ (hvle : aw ≤ (α + ε) - ε), v ≤ aw →
      birthSup hLawY aw (structMap hLawY hvle J) ≠ e)
    (he : birthSup hLawY ((α + ε) - ε) J = e) :
    ∃ m : EReal, m ≤ (α : EReal) ∧ closeE ((b : EReal)) ((e : EReal)) ((ε : ℝ)) ∧
      mult (rankFn stageY JY) ((e : EReal), m) ≠ 0
    := by sorry
