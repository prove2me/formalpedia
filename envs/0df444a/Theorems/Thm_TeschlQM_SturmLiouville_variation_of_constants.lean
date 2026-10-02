-- Prove2me | Theorems.Thm_TeschlQM_SturmLiouville_variation_of_constants
-- name    : TeschlQM.SturmLiouville.variation_of_constants
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:46:36.159326+00:00
-- url     : https://prove2.me/theorems/95cdc896-dcfa-49a2-b6a6-c4810de9703d
-- title:
--   Lemma 9.2 — variation of constants
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data, $z \in \mathbb{C}$, and $g$ with $rg \in L^1_{loc}(I)$. Suppose $u_1, u_2$ are solutions of $(\tau - z)u = 0$ with $W(u_1, u_2) = 1$, and fix $c \in I$. Then every solution $f$ of $(\tau - z) f = g$ can be written, for some $\alpha, \beta \in \mathbb{C}$ and all $x \in I$, as
--   $$f(x) = u_1(x)\Big(\alpha + \int_c^x u_2 g\, r\,dy\Big) + u_2(x)\Big(\beta - \int_c^x u_1 g\, r\,dy\Big),$$
--   $$(pf')(x) = (pu_1')(x)\Big(\alpha + \int_c^x u_2 g\, r\,dy\Big) + (pu_2')(x)\Big(\beta - \int_c^x u_1 g\, r\,dy\Big).$$
--
--   The formula expresses solutions of the inhomogeneous equation through a fundamental system, and underlies the Green function of Lemma 9.7.
--
--   **Formalization Note.** The book states the second line for $f'$; here it is stated for the quasi-derivatives (the book's line multiplied by $p$), which holds at every point of $I$. $W(u_1,u_2) = 1$ is stated as $W_x(u_1,u_2) = 1$ for all $x \in I$ (the Wronskian of two solutions is constant, (9.6)).
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 183, Lemma 9.2, Eq. (9.10)

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_SolvesTau
import Definitions.Def_TeschlQM_SturmLiouville_wronskian

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl, Lemma 9.2, p. 183. Let `u₁, u₂` solve `(τ − z) u = 0` with `W(u₁, u₂) = 1`. Then every
solution `f` of `(τ − z) f = g` (9.8), `r g ∈ L¹_loc(I)`, has the form (9.10) for some
`α, β ∈ ℂ`. The second line of (9.10), stated in the book for `f′`, is stated here for the
quasi-derivatives `p f′`, `p u₁′`, `p u₂′` (the book's line multiplied by `p > 0`), which holds at
every point of `I`. -/
theorem variation_of_constants (L : SLData) (z : ℂ) (g : ℝ → ℂ)
    (hg : LocallyIntegrableOn (fun x => (L.r x : ℂ) * g x) L.I)
    (u₁ u₂ : ℝ → ℂ) (h₁ : IsSolution L z 0 u₁) (h₂ : IsSolution L z 0 u₂)
    (hW : ∀ x ∈ L.I, wronskian L x u₁ u₂ = 1)
    (c : ℝ) (hc : c ∈ L.I) (f : ℝ → ℂ) (hf : IsSolution L z g f) :
    ∃ α β : ℂ, ∀ x ∈ L.I,
      f x = u₁ x * (α + ∫ y in c..x, u₂ y * g y * (L.r y : ℂ)) +
        u₂ x * (β - ∫ y in c..x, u₁ y * g y * (L.r y : ℂ)) ∧
      quasiDeriv L f x = quasiDeriv L u₁ x * (α + ∫ y in c..x, u₂ y * g y * (L.r y : ℂ)) +
        quasiDeriv L u₂ x * (β - ∫ y in c..x, u₁ y * g y * (L.r y : ℂ)) := by sorry

end TeschlQM.SturmLiouville
