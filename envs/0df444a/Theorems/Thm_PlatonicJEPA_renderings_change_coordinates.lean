-- Prove2me | Theorems.Thm_PlatonicJEPA_renderings_change_coordinates
-- name    : PlatonicJEPA.renderings_change_coordinates
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T12:15:00.416689+00:00
-- url     : https://prove2.me/theorems/2207c27b-e432-4304-b8c8-a1b3ea51918d
-- title:
--   Lemma 1: renderings only change coordinates
-- statement:
--   Let $g:Z\to X$ be injective. Then every embedding $h:Z\to\mathbb{R}^k$ of the world is $f\circ g$ for some encoder $f$ of the modality, and $f\circ g$ determines $f$ on the observations $g(Z)$. For every encoder $f$, the modality's objective equals the world objective of $f\circ g$: $L_m(f)=L_\pi(f\circ g)$.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), Appendix A.2, Lemma 1, p. 20

import Mathlib
import Definitions.Def_PlatonicJEPA_Basic

open MeasureTheory Filter Topology

namespace PlatonicJEPA

theorem renderings_change_coordinates {Z X : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (π : Z → Z → ℝ) (ℓ : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (Ω : Measure (Fin k → ℝ) → EReal) (g : Z → X) (hg : Function.Injective g) :
    (∀ h : Z → Fin k → ℝ, ∃ f : X → Fin k → ℝ, f ∘ g = h) ∧
    (∀ f f' : X → Fin k → ℝ, f ∘ g = f' ∘ g → ∀ x ∈ Set.range g, f x = f' x) ∧
    (∀ f : X → Fin k → ℝ, modalityLoss p π ℓ Ω g f = worldLoss p π ℓ Ω (f ∘ g)) := by sorry

end PlatonicJEPA
