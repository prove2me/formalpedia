-- Prove2me | Theorems.Thm_PersistClust_Count_qse_partner_absorb_gen
-- name    : PersistClust.Count.qse_partner_absorb_gen
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T11:42:22.982683+00:00
-- url     : https://prove2.me/theorems/7a2c9127-e2df-4e70-be26-ade78f680aeb
-- title:
--   QSE partner absorb, level-generic: dichotomy right-branch output over an abstract window yields the partner bar via the census absorb
-- statement:
--   Let stageY be a cluster filtration over levels ℝ with relation field JY satisfying the FiltrationLaw and IsTameModule tameness, with component classes comps stageY JY t, coarsening maps structMap, birth-sup birthSup, rank function rankFn stageY JY and persistence-diagram multiplicity mult. Fix an abstract window with bottom aw and top wtop of length at least 1 (1 ≤ wtop − aw), a cell J at the window top with birth-sup e strictly above the top (wtop < e), and a boundary level v in the window (aw ≤ v ≤ wtop); e lies in the ε-band around b (b − ε ≤ e ≤ b + ε). Assume the dichotomy right-branch output over the window: above v, at every level ξ with v < ξ ≤ wtop the descent of J has birth-sup exactly e (hAbove); strictly between aw and v the descent of J never has birth-sup e (hBelow); and if v sits at the window bottom, the descent of J at aw does not have birth-sup e (hbot). Conclusion: b and e are ε-close (closeE b e ε) and the diagram records the partner bar at (e, v): mult (rankFn stageY JY) ((e : EReal), (v : EReal)) ≠ 0. There is no death pin — the callers assemble the QSE death disjunction at the raw break v themselves. The ε-closeness is the band hypothesis; the multiplicity is forced by the census absorb at (e, v) in three window cases: (i) v at the window top — the stable-gap package around (e, v) applies (e > wtop = v) and the thread hypothesis for the absorb is witnessed by the alive-up lift: for every probe η in the gap there is a level-(v+η) cell with birth-sup e (hAbove, since v + η ≤ wtop), whose descent to v − η does not have birth-sup e (hBelow); (ii) v at the window bottom — hbot gives the thread's below-value difference at aw, and descent monotonicity of birth-sups (birth-sups only grow under descent) turns the top thread into the required shape; (iii) v interior — the same absorb with the window-fitted gap (shrunk by the distances v − aw and wtop − v, positive since the window has length ≥ 1), using hAbove above and hBelow below. In each case the census absorb concludes mult (rankFn stageY JY) ((e : EReal), (v : EReal)) ≠ 0. This is the level-generic form of the partner absorb: the image level (α+ε)−ε of the hardwired version is abstracted to wtop and the window bottom α−1 to aw, so the hQP high-lift fill can run its dichotomy at an image level β − ε > α where the hardwired version no longer applies.
-- source:
--   T5c Route A absorb, level-generic form (qseDry12) of the persistence-clustering deliverable (RR-6968, Theorem 4.5 cluster): the partner absorb with the image level (α+ε)−ε abstracted to an arbitrary window top wtop and the window bottom α−1 abstracted to aw, no death pin — the callers assemble the QSE death disjunction at the raw break v themselves (t5_partnerAbsorbGen in the rankKill master, Scratch_rankR1 L7288-7405, ported verbatim from the qseDry1 development, combo26-verified); the hQP high-lift fill runs its dichotomy at the image level β − ε > α where the hardwired t5_partnerAbsorb no longer applies; consumed by the QSE partner-high fill.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem qse_partner_absorb_gen {ιY : Type*} {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawY : FiltrationLaw stageY JY) (hTameY : IsTameModule stageY JY)
    {ε b e aw wtop v : ℝ} {J : comps stageY JY wtop}
    (hband_lo : b - ε ≤ e) (hband_hi : e ≤ b + ε)
    (hwtope : wtop < e) (hawlen : 1 ≤ wtop - aw)
    (hvlo : aw ≤ v) (hvhi : v ≤ wtop)
    (hAbove : ∀ (ξ : ℝ) (hξ : ξ ≤ wtop), v < ξ →
      birthSup hLawY ξ (structMap hLawY hξ J) = e)
    (hBelow : ∀ (ξ : ℝ) (hξ : ξ ≤ wtop), aw ≤ ξ → ξ < v →
      birthSup hLawY ξ (structMap hLawY hξ J) ≠ e)
    (hbot : ∀ (hvle : aw ≤ wtop), v ≤ aw →
      birthSup hLawY aw (structMap hLawY hvle J) ≠ e)
    (he : birthSup hLawY wtop J = e) :
    closeE ((b : EReal)) ((e : EReal)) ((ε : ℝ)) ∧
      mult (rankFn stageY JY) ((e : EReal), ((v : EReal))) ≠ 0
    := by sorry
