-- Prove2me | Theorems.Thm_StableVotingDistortion_eq_27
-- name    : StableVotingDistortion.eq_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:04:00.455447+00:00
-- url     : https://prove2.me/theorems/a893e27b-2fae-49df-84bf-0a06668a4406
-- title:
--   Equation (27) — the layer-cake identity $\int_0^\infty q_v=L_v$ and $z_v(t+R_v)\le q_v(t)$
-- statement:
--   Let $D$ be a lottery, $\rho:C\to\mathbb R_{\ge0}$ with $\rho(a^\star)=0$, and $v$ a voter. Then $q_v$ is integrable on $(0,\infty)$,
--   $$\int_0^\infty q_v(t)\,dt=L_v,$$
--   and for every $t\ge0$,
--   $$z_v(t+R_v)\le q_v(t),\qquad q_v(t)\le s_v.$$
--
--   Differences from the source:
--   - generalization: §6.3.1's setting: $D$ a $g_\phi$-stable lottery, $\phi$ satisfying (26) → any lottery `D ∈ stdSimplex ℝ C`, no $\phi$; reason: (27) is a layer-cake identity and an ordering fact on one rank line; neither stability nor $\phi$ enters; a $g_\phi$-stable lottery is a lottery, so the statement specializes to the page's
--   - encoding: $\int_0^\infty q_v(t)\,dt=L_v$ → also `IntegrableOn` of $q_v$ on `Set.Ioi 0`; reason: a Bochner integral of a non-integrable function is $0$, so the identity needs integrability to say what the page says; $q_v$ is bounded and vanishes for large $t$
--   - encoding: $\rho:C\to\mathbb R_{\ge0}$ → `ρ : C → ℝ` with `∀ c, 0 ≤ ρ c`; reason: the same functions
--   - encoding: $n$ voters and a finite set $C$ → `[Fintype V] [Nonempty V] [Fintype C] [Nonempty C]`, with `V C : Type`; reason: an expectation over voters and a lottery over candidates need both nonempty
-- source:
--   Cai, Frank, Hastings, Ramakrishnan, Wang, Ye, Stable Voting Rules on the Edge of Optimal Metric Distortion, arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equation (27), p.27

import Mathlib
import Definitions.Def_PctDistortion_Election
import Definitions.Def_StableVotingDistortion_rhoV
import Definitions.Def_StableVotingDistortion_slices

set_option autoImplicit false

open PctDistortion

namespace StableVotingDistortion

/-- **Equation (27).** For any lottery `D`, `ρ ≥ 0` with `ρ(a⋆) = 0` and any voter `v`:
`∫_0^∞ q_v(t) dt = L_v`, and for every `t ≥ 0`, `z_v(t + R_v) ≤ q_v(t)` and `q_v(t) ≤ s_v`.

Cai et al., arXiv:2609.08259 (held version, sha256 cfdd5f3d…), §6.3.1, Equation (27), p.27: "Since ρ(a⋆) = 0, we have a⋆ ∉ S_t, and therefore q_v(t) ≤ s_v for all
t ≥ 0. Observe that q_v(t) and z_v(t) satisfy ∫_0^∞ q_v(t) dt = L_v, z_v(t + R_v) ≤ q_v(t). (27)"

**Formalization Note.** Integrability of `q_v` on `(0, ∞)` is part of the conclusion, since a Bochner
integral of a non-integrable function would be `0`. -/
theorem eq_27 {V C : Type} [Fintype V] [Nonempty V] [Fintype C] [Nonempty C] (E : Election V C)
    {D ρ : C → ℝ} (hD : D ∈ stdSimplex ℝ C) (hρ : ∀ c, 0 ≤ ρ c) {aStar : C} (hstar : ρ aStar = 0)
    (v : V) :
    MeasureTheory.IntegrableOn (qv E D ρ v) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi (0 : ℝ), qv E D ρ v t = Lv E D ρ v ∧
      (∀ t, 0 ≤ t → zv E D ρ v (t + Rv E ρ v) ≤ qv E D ρ v t) ∧
      ∀ t, 0 ≤ t → qv E D ρ v t ≤ sv E D aStar v := by sorry

end StableVotingDistortion
