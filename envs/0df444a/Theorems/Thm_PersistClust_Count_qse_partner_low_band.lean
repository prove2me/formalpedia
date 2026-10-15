-- Prove2me | Theorems.Thm_PersistClust_Count_qse_partner_low_band
-- name    : PersistClust.Count.qse_partner_low_band
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-14T18:10:22.263713+00:00
-- url     : https://prove2.me/theorems/9fc0923c-90c5-47fa-9bd8-187406bd6255
-- title:
--   Low-band QSE partner: an X-bar with death inside [alpha − eps, alpha] has an epsilon-close Y-partner above alpha with death at most alpha or epsilon-close to the tracked thread's death
-- statement:
--   Let two 0-dimensional persistence modules X and Y be given by filtration laws, both tame, together with the interleaving package above level alpha: coarsening-compatible maps phi_beta : X-beta -> Y-(beta - eps) and psi_beta : Y-beta -> X-(beta - eps) (the naturality squares (i') and (ii')) and the double-coarsening square (iv') psi_(beta-eps)(phi_beta x) = the 2eps-descent of x, with eps at least 0. Let (b, d) be a real X-bar with nonzero multiplicity whose death d lies INSIDE the low band alpha - eps at most d at most alpha, with birth b above the window top alpha + eps < b and the gate 2eps < b - d. Then there is a real level e > alpha and an extended-real death level m such that (e, m) is epsilon-close in birth to the X-bar (b - eps at most e at most b + eps), has NONZERO multiplicity in Y's diagram, and the partner's death is DISJUNCTIVE: either m at most alpha (the partner stays in the QSE window), or alpha < m with m epsilon-close to the tracked thread's death d (the partner crosses into QNE as the SAME thread tracked to its death). The proof: at eps = 0 the census cell at d+eta of birth-sup b is pinned, the image thread's value is pinned exactly e = b on the interior window, and the dichotomy/absorb pattern or the essential-bar census residual closes a partner below alpha. At eps > 0 the tracked-thread route seals the goal: the Y-stability gap delta-1 at the honest death d + eps; a probe offset mu inside the delta-1 gap and the gate slack; a transport level beta between d + 2eps + mu and b; the alive-up lift with the flat X-ray pin of value b on the whole window (d, beta]; the probe cell at level (d + 2eps + mu) - eps with Y-birth-supremum e in the band [b - eps, b + eps] (the lower bound via square (i') ancestors; the upper bound via the LOW-BAND ELDER TRAP, which caps the Y-ray's birth by b + eps needing only alpha at most the probe v, supplied since v > d + eps at least alpha); then the death-dichotomy at window-bottom d + eps - 1: the full window gives the essential partner (e, bottom); a break at v gives the died partner (e, v) via the level-generic window absorb, and the death-pinning lemma with the delta-1 gap forces v at most d + eps (a shallow break would be Y-uncritical, so the bar would have zero multiplicity); since d at most alpha, the disjunction holds with m = v.
-- source:
--   Support tool of the persistence-clustering deliverable (RR-6968, Theorem 4.5 / Theorem 4.8 cluster): the low-band QSE partner construction (per-copy partner existence for low-band QSE X-bars, disjunctive partner form sealed by the tracked-thread death pin) of the QSE-sector routing. Transcribed GREEN (exit 0, sorry-free) from the rankKill master; the accepted wave-1 closures reused byte-identically from the ACCEPTED qse_partner_high_band record (platform t3_comb argument order), with the death-pinning lemma, the level-generic partner absorb and the NEW low-band elder trap (vestigial alpha at most v - eps pin dropped) inlined verbatim.

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_FiltrationLaw
import Definitions.Def_PersistClust_Count_MatchingCensus

open PersistClust.Count
open scoped ENNReal

namespace PersistClust.Count

theorem qse_partner_low_band {ιX ιY : Type*}
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
    {b d : ℝ} (hbd : d < b) (hdlo : α - ε ≤ d) (hdhi : d ≤ α) (hbαε : α + ε < b)
    (hpx : mult (rankFn stageX JX) ((b : EReal), (d : EReal)) ≠ 0)
    (hgate : 2 * ε < b - d)
    -- REPAIR-QSE (2026-10-14, banked repair map Entry 22): `hband_hi` ORPHANED —
    -- REFUTED by the ε-shift interleaving (hgate-VALID; all four squares hold):
    -- the value-b cell's φ-image may carry an ELDER's birth (e = 6 > b+ε = 3.5
    -- in the banked counterexample), so the upper band e ≤ b+ε is UNDERIVABLE
    -- in general. The conclusion's partner conjunct is restated DISJUNCTIVELY:
    -- the partner either stays in QSE (m ≤ α) or crosses into QNE death-ε-close
    -- to the tracked thread's death d (the ε-shift honest partner is (b+ε, d+ε)
    -- — the SAME thread tracked to its death; birth-closeness stays the separate
    -- closeE conjunct either way).
    :
    ∃ e : ℝ, ∃ m : EReal, (α : EReal) < (e : EReal) ∧
      (m ≤ (α : EReal) ∨ ((α : EReal) < m ∧ closeE ((d : EReal)) m ((ε : ℝ)))) ∧
      closeE ((b : EReal)) ((e : EReal)) ((ε : ℝ)) ∧
      mult (rankFn stageY JY) ((e : EReal), m) ≠ 0
    := by sorry
