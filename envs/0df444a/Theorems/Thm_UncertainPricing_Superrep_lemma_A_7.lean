-- Prove2me | Theorems.Thm_UncertainPricing_Superrep_lemma_A_7
-- name    : UncertainPricing.Superrep.lemma_A_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:38.786951+00:00
-- url     : https://prove2.me/theorems/3b821223-5f7a-4977-a8d1-e5a84f755125
-- title:
--   Lemma A.7, p. 25 — if f, g ∈ ℒ and f ≤ g P-a.s. for every P ∈ P, then f ≤ g quasi-everywhere
-- statement:
--   Let $\mathbf P$ be a set of martingale measures on the canonical space $\Omega$ satisfying $H(\bar\mu)$, let $c$ be the associated capacity and $\mathcal L$ the completion of $C_b(\Omega)$ for $c$.
--
--   If $f,g\in\mathcal L$ satisfy $f\le g$ $P$-almost surely for every $P\in\mathbf P$, then
--   $$f\le g\quad\text{quasi-everywhere, i.e. outside a set }A\text{ with }c(A)=0.$$
--
--   The lemma transfers $P$-a.s. inequalities, obtained under each model separately (e.g. from the Itô formula), to the quasi-sure inequalities that enter the definition of $\Lambda$.
--
--   **Formalization Note.** "Quasi-everywhere" is the capacity-based quasi-sure notion of the definitions file; the polar set need not be measurable. The standing hypothesis $H(\bar\mu)$ of §2 is included (the proof uses the regularity of $c$, Lemma A.3, which rests on it).
-- source:
--   Denis & Martini, arXiv:math/0607111v1, Lemma A.7, p. 25

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction

theorem lemma_A_7 (T : ℝ) (hT : 0 < T) (μU : StieltjesFunction ℝ) (hμU : IsDistFn T μU)
    (Ps : Set (Measure (Ω T))) (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypU μU P)
    (f g : Ω T → ℝ) (hf : InL Ps f) (hg : InL Ps g) (hfg : ∀ P ∈ Ps, f ≤ᵐ[P] g) :
    QS Ps (fun ω => f ω ≤ g ω) := by sorry

end UncertainPricing.Superrep
