-- Prove2me | Theorems.Thm_QuantumZipper_Welding_proposition_1_7
-- name    : QuantumZipper.Welding.proposition_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:59.373978+00:00
-- url     : https://prove2.me/theorems/0d2683bb-0745-4c89-9387-653a3ff348a3
-- title:
--   Proposition 1.7 — the $\gamma$-quantum wedge is stationary under shifting the origin by quantum length $L$
-- statement:
--   Fix $\gamma\in(0,2)$ and $L>0$, and let $(\mathbb H,h)$ be a $\gamma$-quantum wedge. Choose $y>0$ with $\nu_h[0,y]=L$, and let $h^*=h(\cdot+y)$, so that $y$ becomes the origin. Then $(\mathbb H,h^*)$ is again a $\gamma$-quantum wedge.
--
--   The proposition is the quantum analogue of the invariance of $\mathbb H$ under horizontal translations. It underlies the zipper stationarity of Theorem 1.8.
--
--   **Formalization Note** "Is a $\gamma$-quantum wedge" means equality in law of canonical descriptions (p. 21). The canonical description of $h^*$ has arc averages $h_{a\varepsilon}(az+y)+Q\log a$, where $a$ is the radius with $\mu_{h^*}(B_a(0))=1$. The conclusion equates every finite-dimensional law of these arc averages with the corresponding law for the canonical description of any $\gamma$-quantum wedge realization. The arc averages determine the law of the field.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Proposition 1.7, p. 25

import Mathlib
import Definitions.Def_QuantumZipper_Welding_Setting
import Definitions.Def_QuantumZipper_Welding_QuantumLength
import Definitions.Def_QuantumZipper_Welding_Wedge

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper.Welding

universe u v

/-- **Proposition 1.7** (Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2,
Proposition 1.7, p. 25). Fix `L > 0` and let `(ℍ, h)` be a `γ`-quantum wedge. Choose `y > 0` with
`ν_h[0, y] = L` and let `h* = h(· + y)`. Then `(ℍ, h*)` is a `γ`-quantum wedge.

**Formalization Note**
* `(ℍ, h)` is a `γ`-quantum wedge field (1.10) (`IsWedgeField γ γ`), with quantum area `μ` and
  boundary length `ν` (on all of `ℝ`); `Y ω` is the point with `ν_h[0, Y] = L`.
* "`(ℍ, h*)` is a `γ`-quantum wedge" is equality in law of doubly marked quantum surfaces, i.e. of
  canonical descriptions (p. 21). The canonical description of `h*` is `h*(a·) + Q log a` with `a` the
  radius at which the area measure `μ_{h*} = μ_h(· + Y)` gives mass `1` to `B_a(0)`; its arc average
  over `σ_{z,ε}` is `h_{aε}(az + Y) + Q log a`. The conclusion equates every finite-dimensional law of
  these arc averages (which determine the law of the field) with the corresponding law for the
  canonical description of any `γ`-quantum wedge realization `(Ω', P', W₁', W₂', Ψ')`.
* `γ ∈ (0, 2)` (the setting of §1.6). -/
theorem proposition_1_7 {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (L : ℝ) (hL : 0 < L)
    (W₁ W₂ : ℝ≥0 → Ω → ℝ) (Ψ : Ω → Measure ℂ → ℝ) (hw : IsWedgeField γ γ P W₁ W₂ Ψ)
    (μ : Ω → Measure ℂ) (hμ : ∀ᵐ ω ∂P, IsAreaMeasureOn γ Hplane (arcAvg (Ψ ω)) (μ ω))
    (ν : Ω → Measure ℝ)
    (hν : ∀ᵐ ω ∂P, IsBoundaryLengthOn γ Set.univ (fun x ε => arcAvg (Ψ ω) (x : ℂ) ε) (ν ω))
    (Y : Ω → ℝ) (hY : ∀ᵐ ω ∂P, 0 < Y ω ∧ ν ω (Set.Icc 0 (Y ω)) = ENNReal.ofReal L)
    (Ω' : Type v) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W₁' W₂' : ℝ≥0 → Ω' → ℝ) (Ψ' : Ω' → Measure ℂ → ℝ) (hw' : IsWedgeField γ γ P' W₁' W₂' Ψ')
    (μ' : Ω' → Measure ℂ) (hμ' : ∀ᵐ ω' ∂P', IsAreaMeasureOn γ Hplane (arcAvg (Ψ' ω')) (μ' ω')) :
    ∀ (n : ℕ) (z : Fin n → ℂ) (ε : Fin n → ℝ), (∀ j, 0 ≤ (z j).im ∧ 0 < ε j) →
      P.map (fun ω => fun j =>
          let a := canonicalRadius ((μ ω).map (fun w => w - (Y ω : ℂ)))
          arcAvg (Ψ ω) ((a : ℂ) * z j + (Y ω : ℂ)) (a * ε j) + Qc γ * Real.log a) =
        P'.map (fun ω' => fun j => canonicalArcAvg (Qc γ) (Ψ' ω') (μ' ω') (z j) (ε j)) := by sorry

end QuantumZipper.Welding
