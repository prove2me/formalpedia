-- Prove2me | Theorems.Thm_SurgeSpatial_Attraction_lemma_A_2
-- name    : SurgeSpatial.Attraction.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:42.889754+00:00
-- url     : https://prove2.me/theorems/3394cbff-eb31-4a31-a2b0-947d8af2843e
-- title:
--   Lemma A-2, p. A-2 — equilibrium utilities: U = V_B = V for T₂-a.e. y ∈ B, and U ≤ V_B Γ-a.e. on B
-- statement:
--   Let $(p,\mathcal T)$ be a feasible solution of (P2) (a price mapping and a corresponding equilibrium), and let $B\subseteq\mathcal C$ be measurable with $\Gamma(B)>0$. Then
--   $$U\big(y,p(y),s^{\mathcal T}(y)\big)=V_B(y\mid p,\mathcal T)=V(y\mid p,\mathcal T)\qquad \mathcal T_2\text{-a.e. } y\in B,$$
--   and
--   $$U\big(y,p(y),s^{\mathcal T}(y)\big)\le V_B(y\mid p,\mathcal T)\qquad \Gamma\text{-a.e. } y\in B.$$
--
--   Wherever drivers end up in equilibrium, staying there is as good as any move; this is the step that turns the platform's revenue into the (P2) objective.
--
--   **Formalization Note** Measurability of $B$ is carried over from Lemma 1, which the proof uses. $\mathcal T_2$ is the second marginal `T.map Prod.snd`.
-- source:
--   Besbes, Castro, Lobel, Surge Pricing and its Spatial Supply Response, SSRN 3124571 (version of May 17, 2019), p. A-2, Lemma A-2

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting
open MeasureTheory

namespace SurgeSpatial.Attraction

theorem lemma_A_2 (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) (B : Set E) (hB : MeasurableSet B) (hBC : B ⊆ M.C)
    (hΓB : 0 < M.Γ B) :
    (∀ᵐ y ∂(T.map Prod.snd), y ∈ B → M.U p T y = M.VB B p T y ∧ M.VB B p T y = M.V p T y) ∧
      (∀ᵐ y ∂M.Γ, y ∈ B → M.U p T y ≤ M.VB B p T y) := by sorry

end SurgeSpatial.Attraction
