-- Prove2me | Theorems.Thm_PrideGuilt_Supplement_theorem_3
-- name    : PrideGuilt.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:26:38.875973+00:00
-- url     : https://prove2.me/theorems/d70a80dc-dff7-5518-82e1-9b19e0262ceb
-- title:
--   Theorem 3 — the optimal profit is continuous at the region boundaries and nondecreasing in $\gamma_P,\gamma_G$ on $\Omega_1,\Omega_2,\Omega_3$ (corrected: demand $D\ge0$)
-- statement:
--   Assume the paper's standing assumptions and let $\Pi^*(\gamma_P,\gamma_G)$ be the manufacturer's optimal profit, the supremum of $\Pi(p,f)$ over $(p,f)\in\mathbb R^2$ with $D(p,f)\ge0$. Let $S=\{(\gamma_P,\gamma_G):\gamma_P>0,\ \gamma_G>0,\ \gamma_P\ne\gamma_G\}$ and consider the regions $\Omega_1,\Omega_2^0,\Omega_2^1,\Omega_3,\Omega_4$ of Propositions 2–5. Then:
--
--   1. $\Pi^*$ is continuous at every point of $S$ that lies in the closures of two different regions among $\Omega_1,\Omega_2^0,\Omega_2^1,\Omega_3,\Omega_4$, or of two different regions among $\Omega_1,\Omega_2,\Omega_3,\Omega_4$.
--   2. At every diagonal point $(\gamma,\gamma)$ with $\gamma>0$ lying in the closures of both $\Omega_2^1$ and $\Omega_3$, writing $\Delta\gamma=\gamma_P-\gamma_G$,
--   $$
--   \lim_{\Delta\gamma\uparrow0}\Pi^*=\lim_{\Delta\gamma\downarrow0}\Pi^*,
--   $$
--   that is, the limits of $\Pi^*$ at $(\gamma,\gamma)$ from the half-plane $\gamma_P<\gamma_G$ and from the half-plane $\gamma_P>\gamma_G$ exist and are equal.
--   3. For every $\gamma_G>0$, the map $\gamma_P\mapsto\Pi^*(\gamma_P,\gamma_G)$ is nondecreasing on $\{\gamma_P>0,\ \gamma_P\ne\gamma_G,\ (\gamma_P,\gamma_G)\in\Omega_k\}$ for each of $\Omega_k=\Omega_1,\Omega_2,\Omega_3$.
--   4. For every $\gamma_P>0$, the map $\gamma_G\mapsto\Pi^*(\gamma_P,\gamma_G)$ is nondecreasing on $\{\gamma_G>0,\ \gamma_G\ne\gamma_P,\ (\gamma_P,\gamma_G)\in\Omega_k\}$ for each of $\Omega_k=\Omega_1,\Omega_2,\Omega_3$.
--
--   Outside $\Omega_4$ stronger emotions never hurt the manufacturer, and although the equilibrium recycling rate jumps from $0$ to $1$ across the boundary of $\Omega_2^0$ and $\Omega_2^1$, the optimal profit does not jump.
--
--   **Formalization Note** $\Pi^*$ is one function on $S$ (the base mission's `optProfit`); each proposition evaluates it region by region. Continuity is stated within $S$, which is open, so it is continuity at the point. The regions $\Omega_1,\Omega_2,\Omega_3,\Omega_4$ are listed besides the sub-regions because $\Omega_2^0\cup\Omega_2^1$ does not cover $\Omega_2$ when $\tau^0=1$ or $b_1=b_0$. $\Pi^*$ is not evaluated on the diagonal, which belongs to no region (footnote 5).
--
--   Differences from the source:
--   - correction: Π* is the maximum of Π(p, f) over all (p, f), eq. (5), with no constraint → Π* and "optimal" over (p, f) ∈ ℝ² with D(p, f) ≥ 0 (the published optProfit and its feasible set); reason: as printed, (5) has no maximum when b1 < b0: with τ* = 1 and f → ∞, a negative demand times a negative margin is unbounded (e.g. b0 = 1, b1 = 1/2, cn = 1, cu = 1/2, ce = 3/2, IP = IG = 0 at any (γP, γG)); the base mission declared this correction, footnote 4 and p.12 show feasible demand is intended
--   - reading: "Π*, as it is defined in each region, is continuous at all region boundaries" → ContinuousWithinAt Π* S x at every x ∈ S lying in the closures of two distinct regions among Ω1, Ω2^0, Ω2^1, Ω3, Ω4, or among Ω1, Ω2, Ω3, Ω4; reason: Π* is a single function on S; the second family is needed because Ω2^0 ∪ Ω2^1 does not cover Ω2 when τ0 = 1 or b1 = b0; a boundary point is a point of S adjacent to two regions; S is open, so this is continuity at x
--   - encoding: "at the boundary between Ω2^1 and Ω3, lim_{Δγ↑0} Π* = lim_{Δγ↓0} Π*, where Δγ = γP − γG" → at every (γ, γ), γ > 0, in the closures of Ω2^1 and Ω3: ∃ L, Π* → L along 𝓝[{γP < γG}] (γ, γ) and along 𝓝[{γG < γP}] (γ, γ); reason: Δγ ↑ 0 and Δγ ↓ 0 are the approaches from the two half-planes; the diagonal itself is not in S
--   - reading: "∂Π*/∂γP ≥ 0 in Ω1, Ω2 and Ω3", "∂Π*/∂γG ≥ 0 in Ω1, Ω2 and Ω3" → MonotoneOn of the sections γP ↦ Π*(γP, γG) and γG ↦ Π*(γP, γG) on the part of each region in S; reason: Π* is not differentiable on the Ω2^0/Ω2^1 boundary inside Ω2 (constant on one side, increasing on the other), so the derivative condition is read as nondecreasing in each variable, which is what the derivative sign expresses where it exists
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Theorem 3, p.19; footnote 5, p.15

import Mathlib
import Definitions.Def_PrideGuilt_Standing
import Definitions.Def_PrideGuilt_optProfit
import Definitions.Def_PrideGuilt_InOmega4
import Definitions.Def_PrideGuilt_Supplement_InOmega1
import Definitions.Def_PrideGuilt_Supplement_InOmega2Zero
import Definitions.Def_PrideGuilt_Supplement_InOmega2One
import Definitions.Def_PrideGuilt_Supplement_InOmega3

open Filter Topology

namespace PrideGuilt.Supplement

open PrideGuilt

/-- **Theorem 3 (continuity and monotonicity of the optimal profit outside `Ω₄`), with the base
mission's demand constraint `D ≥ 0`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Theorem 3, p.19 (PDF 20).

Under the standing assumptions, let `S = {(γ_P, γ_G) | γ_P > 0, γ_G > 0, γ_P ≠ γ_G}` and consider
the regions `Ω₁, Ω₂⁰, Ω₂¹, Ω₃, Ω₄` of Propositions 2–5. Then, for the optimal profit `Π*`:
(i) `Π*` is continuous (within `S`) at every point of `S` that lies in the closures of two
  different regions among `Ω₁, Ω₂⁰, Ω₂¹, Ω₃, Ω₄`, or of two different regions among
  `Ω₁, Ω₂, Ω₃, Ω₄`; and at every diagonal point `(γ, γ)`, `γ > 0`, lying in the closures of both
  `Ω₂¹` and `Ω₃`, the limits of `Π*` from the side `Δγ = γ_P − γ_G < 0` and from the side
  `Δγ > 0` exist and are equal;
(ii) for every `γ_G > 0`, `γ_P ↦ Π*(γ_P, γ_G)` is nondecreasing on the part of each of `Ω₁`, `Ω₂`
  and `Ω₃` with `γ_P > 0`, `γ_P ≠ γ_G`;
(iii) for every `γ_P > 0`, `γ_G ↦ Π*(γ_P, γ_G)` is nondecreasing on the part of each of `Ω₁`, `Ω₂`
  and `Ω₃` with `γ_G > 0`, `γ_G ≠ γ_P`.

**Formalization Note.** `Π*` is the base mission's `optProfit`, one function on `S` (supremum
over `D ≥ 0`); "`Π*`, as it is defined in each region" is that function, which each proposition
evaluates region by region. A "region boundary" point is a point of `S` in the closures of two
different regions. The family `Ω₁, Ω₂, Ω₃, Ω₄` is listed as well because `Ω₂⁰ ∪ Ω₂¹` does not
cover `Ω₂` when `τ⁰ = 1` or `b₁ = b₀` (both sub-regions are then empty), and the page's "all region
boundaries" includes the boundary of `Ω₂` in those cases too. Since `S` is open, continuity within `S` there is continuity at the point. The
diagonal is outside `S`; `Π*` is not evaluated there. "`∂Π*/∂γ_P ≥ 0` in `Ω₂`" is read as
monotonicity of the sections: `Π*` is not differentiable on the `Ω₂⁰`/`Ω₂¹` boundary inside `Ω₂`,
where it is constant on one side and increasing on the other. -/
theorem theorem_3 (P : Params) (hP : Standing P) :
    let S : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2 ∧ q.1 ≠ q.2}
    let V : ℝ × ℝ → ℝ := fun q => optProfit P q.1 q.2
    let R : Fin 5 → Set (ℝ × ℝ) :=
      ![{q | InOmega1 P q.1 q.2}, {q | InOmega2Zero P q.1 q.2}, {q | InOmega2One P q.1 q.2},
        {q | InOmega3 P q.1 q.2}, {q | InOmega4 P q.1 q.2}]
    let T : Fin 4 → Set (ℝ × ℝ) :=
      ![{q | InOmega1 P q.1 q.2}, {q | InOmega2 P q.1 q.2}, {q | InOmega3 P q.1 q.2},
        {q | InOmega4 P q.1 q.2}]
    -- (i) continuity at region boundaries: between the sub-regions Ω₁, Ω₂⁰, Ω₂¹, Ω₃, Ω₄ ...
    (∀ x ∈ S, ∀ i j : Fin 5, i ≠ j → x ∈ closure (R i) → x ∈ closure (R j) →
        ContinuousWithinAt V S x) ∧
    -- ... and between the regions Ω₁, Ω₂, Ω₃, Ω₄ themselves
    (∀ x ∈ S, ∀ i j : Fin 4, i ≠ j → x ∈ closure (T i) → x ∈ closure (T j) →
        ContinuousWithinAt V S x) ∧
    -- (i) equal one-sided limits across the diagonal between Ω₂¹ and Ω₃
    (∀ γ : ℝ, 0 < γ → (γ, γ) ∈ closure (R 2) → (γ, γ) ∈ closure (R 3) →
        ∃ L : ℝ, Tendsto V (𝓝[{q | q.1 < q.2}] (γ, γ)) (𝓝 L) ∧
          Tendsto V (𝓝[{q | q.2 < q.1}] (γ, γ)) (𝓝 L)) ∧
    -- (ii) monotone in γ_P on Ω₁, Ω₂, Ω₃
    (∀ γG : ℝ, 0 < γG →
        MonotoneOn (fun x => optProfit P x γG) {x | 0 < x ∧ x ≠ γG ∧ InOmega1 P x γG} ∧
        MonotoneOn (fun x => optProfit P x γG) {x | 0 < x ∧ x ≠ γG ∧ InOmega2 P x γG} ∧
        MonotoneOn (fun x => optProfit P x γG) {x | 0 < x ∧ x ≠ γG ∧ InOmega3 P x γG}) ∧
    -- (iii) monotone in γ_G on Ω₁, Ω₂, Ω₃
    (∀ γP : ℝ, 0 < γP →
        MonotoneOn (fun y => optProfit P γP y) {y | 0 < y ∧ y ≠ γP ∧ InOmega1 P γP y} ∧
        MonotoneOn (fun y => optProfit P γP y) {y | 0 < y ∧ y ≠ γP ∧ InOmega2 P γP y} ∧
        MonotoneOn (fun y => optProfit P γP y) {y | 0 < y ∧ y ≠ γP ∧ InOmega3 P γP y}) := by sorry

end PrideGuilt.Supplement
