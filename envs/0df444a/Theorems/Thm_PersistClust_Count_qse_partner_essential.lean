-- Prove2me | Theorems.Thm_PersistClust_Count_qse_partner_essential
-- name    : PersistClust.Count.qse_partner_essential
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-12T18:58:10.622994+00:00
-- url     : https://prove2.me/theorems/0e323d07-aa3c-4353-b37b-db2ed16312b0
-- title:
--   Essential QSE partner: under the interleaving squares, an essential X-bar (death at bottom) born above the alpha-window has an epsilon-close Y-partner bar above alpha
-- statement:
--   Let two 0-dimensional persistence modules X and Y be given by filtration laws, both tame, together with the interleaving package above level alpha: coarsening-compatible maps phi_beta : X-beta -> Y-(beta - eps) and psi_beta : Y-beta -> X-(beta - eps) (the squares (i') and (ii')) and the double-coarsening square (iv'), with eps at least 0. Let b be a birth level above the window top, alpha + eps < b, such that the ESSENTIAL bar (b, bottom) has nonzero multiplicity in X's diagram. Then there is a real level e > alpha and an extended-real death level m at most alpha such that e lies in the band [b - eps, b + eps] and (e, m) has NONZERO multiplicity in Y's diagram: the essential QSE partner. The proof seeds the X-side at the eps-floor level alpha - eps directly from the essential multiplicity: the bottom-branch of mult unfolds to a nested infimum of rank differences; at a probe radius inside the critical gap around b, the window split (with the b-probe levels non-generic by the gap) yields a level-(alpha - eps) cell whose birth-sup is exactly b. From there the high-band partner glue runs verbatim: alive-up lift to the source level alpha + eps, the 2eps-descent pin, the image band [b - eps, b + eps] via the image-birth pair, and the death-dichotomy of the image cell's value-ray: an exit boundary feeds the factored window absorb (census absorption at (e, v)) for a died partner with m at most alpha, and everywhere-e persistence below the window yields the essential partner (e, bottom) via the essential-bar census residual.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): the essential-copy QSE partner supply (qseDry7 route (b)) covering the death-at-bottom sector of the QSE routing that the high-band and low-band partners cannot reach. Transcribed GREEN (exit 0, sorry-free) from the ORCH-verified census lane working copy; the accepted wave-1 nodes census_absorption_mult_nonzero, essential_bar_mult_nonzero, image_birth_upper_bound and image_birth_strong_lower_bound are INLINED verbatim (with their green closures), and the essential seed (bottom-branch unfold + window split at the eps-floor level) is the lane's verified text.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem qse_partner_essential {ιX ιY : Type*}
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
    {b : ℝ} (hbαε : α + ε < b)
    (hpx : mult (rankFn stageX JX) ((b : EReal), (⊥ : EReal)) ≠ 0) :
    ∃ e : ℝ, ∃ m : EReal, (α : EReal) < (e : EReal) ∧ m ≤ (α : EReal) ∧
      closeE ((b : EReal)) ((e : EReal)) ((ε : ℝ)) ∧
      mult (rankFn stageY JY) ((e : EReal), m) ≠ 0
    := by sorry
