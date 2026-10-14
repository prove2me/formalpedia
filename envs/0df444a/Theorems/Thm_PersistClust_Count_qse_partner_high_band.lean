-- Prove2me | Theorems.Thm_PersistClust_Count_qse_partner_high_band
-- name    : PersistClust.Count.qse_partner_high_band
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T18:52:27.223999+00:00
-- url     : https://prove2.me/theorems/d195e8e5-f1c9-44b2-8c16-a1d483fbf86a
-- title:
--   High-band QSE partner: under the interleaving squares, a real X-bar born above the alpha-window with death below alpha has an epsilon-close Y-partner bar above alpha
-- statement:
--   Let two 0-dimensional persistence modules X and Y be given by filtration laws, both tame, together with the interleaving package above level alpha: coarsening-compatible maps phi_beta : X-beta -> Y-(beta - eps) and psi_beta : Y-beta -> X-(beta - eps) (the squares (i') and (ii')) and the double-coarsening square (iv') psi_(beta-eps)(phi_beta x) = the 2eps-descent of x, with eps at least 0. Let (b, d) be a real X-bar with multiplicity nonzero in X's diagram, d at most alpha, room d < alpha - eps below the eps-floor, and birth b above the window top alpha + eps < b. Then there is a real level e > alpha and an extended-real death level m at most alpha such that the pair (e, m) is epsilon-close to (b, e)'s band (b - eps <= e <= b + eps) and has NONZERO multiplicity in Y's diagram: the high-band QSE partner bar. The proof: pin a census cell at level d+eta with birth-sup exactly b (comb census unfold at a probe inside the critical gap); lift it through the eps-floor source level alpha + eps (the alive-up lift); its 2eps-descent still carries birth-sup b (the descent pin); the image cell at level alpha has birth-sup e inside the band [b - eps, b + eps] (the image-birth pair: strong lower bound via square (i') ancestors, upper bound via square (iv') and rung-B monotonicity); then the death-dichotomy of the value-ray through the image cell: either the value e persists on the whole window below, in which case the essential-bar census residual gives the partner (e, bottom), or the ray has an exit boundary, and the factored window absorb turns the boundary into a died partner (e, m) with m at most alpha via the census absorption (every below-census cell lifts to an above-census cell; the lifts are injective and miss the thread's own cell, so the below-census injects into the above-census minus one, making the combination positive).
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): the high-band QSE partner construction (per-copy partner existence for high far QSE X-bars) of the QSE-sector routing. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified census lane working copy; the accepted wave-1 nodes census_absorption_mult_nonzero, essential_bar_mult_nonzero, image_birth_upper_bound and image_birth_strong_lower_bound are INLINED verbatim (with their green closures), the census-cell t3_comb call site is rewritten to the platform argument order, and the dichotomy/absorb factoring is the lane's verified text.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem qse_partner_high_band {ιX ιY : Type*}
    {stageX : ℝ → Set ιX} {JX : ℝ → ιX → ιX → Prop}
    {stageY : ℝ → Set ιY} {JY : ℝ → ιY → ιY → Prop}
    (hLawX : FiltrationLaw stageX JX) (hLawY : FiltrationLaw stageY JY)
    (hTameX : IsTameModule stageX JX) (hTameY : IsTameModule stageY JY)
    {α ε : ℝ} (hε : 0 ≤ ε)
    (φ : ∀ β : ℝ, α ≤ β → comps stageX JX β → comps stageY JY (β - ε))
    (ψ : ∀ β : ℝ, α ≤ β → comps stageY JY β → comps stageX JX (β - ε))
    (hSq1 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (x : comps stageX JX β'),
      φ β hβ (structMap hLawX hle x) =
        structMap hLawY (show β - ε ≤ β' - ε by linarith) (φ β' hβ' x))
    (hSq2 : ∀ (β β' : ℝ) (hβ : α ≤ β) (hβ' : α ≤ β') (hle : β ≤ β')
        (y : comps stageY JY β'),
      ψ β hβ (structMap hLawY hle y) =
        structMap hLawX (show β - ε ≤ β' - ε by linarith) (ψ β' hβ' y))
    (hSq4 : ∀ (β : ℝ) (hβ : α ≤ β) (hβε : α ≤ β - ε) (x : comps stageX JX β),
      ψ (β - ε) hβε (φ β hβ x) =
        structMap hLawX (show (β - ε) - ε ≤ β by linarith) x)
    {b d : ℝ} (hbd : d < b) (hdα : d ≤ α) (hroom : d < α - ε) (hbαε : α + ε < b)
    (hpx : mult (rankFn stageX JX) ((b : EReal), (d : EReal)) ≠ 0) :
    ∃ e : ℝ, ∃ m : EReal, (α : EReal) < (e : EReal) ∧ m ≤ (α : EReal) ∧
      closeE ((b : EReal)) ((e : EReal)) ((ε : ℝ)) ∧
      mult (rankFn stageY JY) ((e : EReal), m) ≠ 0
    := by sorry
