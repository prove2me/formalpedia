-- Prove2me | Theorems.Thm_VolunteerEngage_Thresholds_Supplement_eq_E8
-- name    : VolunteerEngage.Thresholds.Supplement.eq_E8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T04:12:34.73517+00:00
-- url     : https://prove2.me/theorems/06563afc-de09-4ac0-9ddc-450b3d90dec9
-- title:
--   (E8), Online Supplement p. 12 — the left-continuous minimal maximizer
-- statement:
--   Let $M$ satisfy the model's standing assumptions. Write $\theta_l$ for its drift breakpoints and $c_l$ for its strictly increasing cost slopes. The function $\psi$ defined by (67) is the smallest maximizer, and for every $y\in\mathbb R$,
--
--   $$\psi(y)=\begin{cases}\theta_0,&y\le c_1,\\\theta_{m-1},&c_{m-1}<y\le c_m,\quad 2\le m\le L,\\\theta_L,&c_L<y.\end{cases}$$
--
--   In particular the lower step is chosen at every kink. This identifies the optimizer needed to translate feedback policy (70) into the nested threshold policy (72).
--
--   **Formalization Note** The theorem additionally certifies that the defining infimum is an attained minimum of the maximizing set.
--
--   Differences from the source:
--   - encoding: the queueing primitives and standing assumptions of §§2–3 → M.Standing at every theorem; reason: it expands to L≥1, θ0<0, η_l>0, 0<c_1<⋯<c_L<p and p,κ,σ>0; these are the inherited model assumptions, with no θ_L≥0 restriction
--   - reading: M, ĉ_m, η̂_m in §E → L, c_m, η_m of the main text; reason: these are the same parameters under the supplement notation
--   - encoding: ψ is the minimal maximizer (67) → IsLeast of the maximizing set plus all three branches of (E8); reason: this certifies the meaning of sInf without assuming the closed form or attainment
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, Online Supplement p. 12, (E8); p. 21, (67)

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Supplement_Psi

namespace VolunteerEngage.Thresholds.Supplement

/-- (E8), Online Supplement p. 12. Every branch, with the least maximizer
at each kink. The first conjunct also certifies the infimum as a minimum. -/
theorem eq_E8 (M : Model) (hM : M.Standing) :
    ∀ y : ℝ,
      IsLeast {x : ℝ | x ∈ Set.Icc M.θ0 (M.θ M.L) ∧ y * x - cost M x = phi M y}
        (psi M y) ∧
      (y ≤ M.c 1 → psi M y = M.θ0) ∧
      (∀ m ∈ Finset.Icc 2 M.L, M.c (m - 1) < y → y ≤ M.c m → psi M y = M.θ (m - 1)) ∧
      (M.c M.L < y → psi M y = M.θ M.L) := by sorry

end VolunteerEngage.Thresholds.Supplement
