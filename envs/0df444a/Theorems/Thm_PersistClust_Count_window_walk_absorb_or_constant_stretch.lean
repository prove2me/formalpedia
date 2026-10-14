-- Prove2me | Theorems.Thm_PersistClust_Count_window_walk_absorb_or_constant_stretch
-- name    : PersistClust.Count.window_walk_absorb_or_constant_stretch
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-13T07:21:00.197475+00:00
-- url     : https://prove2.me/theorems/b5135dc8-a650-4008-bd73-2d28514c7e19
-- title:
--   Window walk: a capped in-band cell yields an in-box bar or a constant value stretch
-- statement:
--   Let a 0-dimensional persistence module be given by a filtration law (stage sets with a same-component relation) of finite type (IsTameModule), carrying the critical-set census bookkeeping: critSet is the finite set of critical levels, and birthSup measures the level at which a component class is born. Let b, d, epsilon, beta be levels with d + 2*epsilon < b, 0 <= epsilon, and let alpha' < d - epsilon. Let I be a cell at level w0 with d + epsilon < w0 <= beta - epsilon whose value lies in the band: b - epsilon <= birthSup w0 I. Suppose the value CAP holds: for every probe v with d + epsilon < v <= beta - epsilon, the value of the descended cell is at most b + epsilon. Then EITHER there is an in-box bar: levels b' in [b - epsilon, b + epsilon] and m' in [d - epsilon, d + epsilon] with the diagram multiplicity mult (rankFn stage J) (b', m') nonzero; OR the walk goes constant: there are wtop with d + epsilon < wtop <= w0 and Wbox in [b - epsilon, b + epsilon] such that EVERY descent-level xi in [d - epsilon, wtop] of I has value exactly Wbox - the value is constant along the whole descent stretch from the box bottom up past the box top d + epsilon. The cap is what makes the walk terminate: values can only rise into the capped band, so the escape 'the state value is its own level' is excluded and each jump strictly decreases the finite count of critical levels strictly above the value.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): design part 5, the window walk of the rank lane - it replaces the dichotomy+residue case analysis on an image ray by a terminating descent walk that either emits the in-box bar outright (census absorption at the in-box break) or certifies a constant value stretch feeding the two-walk merge-drop. Designed to consume the cap supplied by the full-cap tool of the same lane (the elder-trap route). Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified rank lane working copy together with its green census machinery (l3-dichotomy, census absorption, stable delta, mult unfolding, combination lemmas); companion of the accepted census_merge_absorption_mult_nonzero, of the accepted theorem_4_5 elder-rule support cluster, of the accepted theorem_4_8_core, and of the accepted theorem_4_8_corrected_tau_excision.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem window_walk_absorb_or_constant_stretch {ι : Type*} {stage : ℝ → Set ι} {J : ℝ → ι → ι → Prop}
    (hLaw : FiltrationLaw stage J) (hTame : IsTameModule stage J)
    {b d ε β α' w₀ : ℝ}
    (hsep : d + 2 * ε < b) (hε0 : 0 ≤ ε) (hα' : α' < d - ε)
    (I : comps stage J w₀)
    (hw₀lo : d + ε < w₀) (hw₀hi : w₀ ≤ β - ε)
    (hW₀lo : b - ε ≤ birthSup hLaw w₀ I)
    (hcap : ∀ v : ℝ, d + ε < v → v ≤ β - ε → ∀ hle : v ≤ w₀,
      birthSup hLaw v (structMap hLaw hle I) ≤ b + ε) :
    (∃ (b' m' : ℝ), b - ε ≤ b' ∧ b' ≤ b + ε ∧ d - ε ≤ m' ∧ m' ≤ d + ε ∧
        mult (rankFn stage J) ((b' : EReal), (m' : EReal)) ≠ 0) ∨
    (∃ (wtop Wbox : ℝ), d + ε < wtop ∧ wtop ≤ w₀ ∧ b - ε ≤ Wbox ∧ Wbox ≤ b + ε ∧
        ∀ (ξ : ℝ) (hle : ξ ≤ w₀), d - ε ≤ ξ → ξ ≤ wtop →
          birthSup hLaw ξ (structMap hLaw hle I) = Wbox)
    := by sorry
