-- Prove2me | Theorems.Thm_QuantumZipper_Welding_proposition_1_6
-- name    : QuantumZipper.Welding.proposition_1_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:18:35.870733+00:00
-- url     : https://prove2.me/theorems/3d77240b-7bb7-42e9-8c04-20e9266eb501
-- title:
--   Proposition 1.6 — zooming in at a quantum-length-typical boundary point gives a $\gamma$-quantum wedge
-- statement:
--   Fix $\gamma\in(0,2)$ and a bounded subdomain $D\subset\mathbb H$ whose boundary meets $\mathbb R$ in a segment $[c,d]$ of positive length. Let $\tilde h$ be the GFF on $D$ with zero boundary conditions on $\partial D\setminus\mathbb R$ and free boundary conditions on $\partial D\cap\mathbb R$. Let $[a,b]\subseteq[c,d]$ with $a<b$, let $\mathfrak h_0$ be continuous on $D$ and extend continuously to $(a,b)$, let $dh$ be the law of $h=\mathfrak h_0+\tilde h$, and assume $\mathbb E\,\nu_h[a,b]<\infty$. Now:
--
--   1. sample $h$ from $\nu_h[a,b]\,dh$, normalized to a probability measure;
--   2. sample $x$ from $\nu_h$ restricted to $[a,b]$, normalized;
--   3. let $h^*=h(\cdot+x)$.
--
--   Then as $C\to\infty$ the doubly marked quantum surfaces $\mathcal S_{h^*+C/\gamma}$ converge in law to a $\gamma$-quantum wedge, in the topology of convergence of doubly marked quantum surfaces.
--
--   Near a point sampled from quantum boundary length, the surface looks like a $\gamma$-quantum wedge. This is the local picture behind Theorem 1.8.
--
--   **Formalization Note** The paper allows $\gamma=0$; there $C/\gamma$ and $Q$ are undefined, so $\gamma>0$ is assumed. The topology is convergence of the canonical area measures on bounded sets (pp. 23–24). Convergence in law is stated through every finite-dimensional law $(\int f_j\,d\mu^{\mathrm{can}})_j$, with $f_j$ continuous of compact support, tested against bounded continuous functions; for random measures this is convergence in law in the vague topology. The sampled law is written as $Z^{-1}\mathbb E\big[\int_{[a,b]}F(\cdots)\,\nu_h(dx)\big]$. Adding $C/\gamma$ multiplies $\mu_h$ by $e^C$, and $\mu_h$ is zero outside $D-x$. The limit is the canonical description of any $\gamma$-quantum wedge realization.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Proposition 1.6, p. 24 (topology pp. 23–24)

import Mathlib
import Definitions.Def_QuantumZipper_Welding_Setting
import Definitions.Def_QuantumZipper_Welding_QuantumLength
import Definitions.Def_QuantumZipper_Welding_Wedge
import Definitions.Def_QuantumZipper_Welding_MixedGFF

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper.Welding

universe u v

/-- **Proposition 1.6** (Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2,
Proposition 1.6, p. 24). Fix `γ ∈ (0, 2)` and a bounded subdomain `D ⊂ ℍ` with `∂D ∩ ℝ = [c, d]`,
`c < d`. Let `h̃` be the GFF on `D` with zero boundary conditions on `∂D \ ℝ` and free boundary
conditions on `∂D ∩ ℝ`, let `[a, b] ⊆ [c, d]`, let `𝔥₀` be continuous on `D` and extend continuously
to `(a, b)`, and let `dh` be the law of `h = 𝔥₀ + h̃`, with `E ν_h[a, b] < ∞`. Sample `h` from
`ν_h[a, b] dh` (normalized), then `x` from `ν_h|_{[a,b]}` (normalized), and let `h* = h(· + x)`. Then
as `C → ∞` the doubly marked quantum surfaces `S_{h* + C/γ}` converge in law to a `γ`-quantum wedge.

**Formalization Note**
* **`γ = 0` is excluded** (the paper says `γ ∈ [0, 2)`): at `γ = 0`, `C/γ` and `Q = 2/γ + γ/2` are
  undefined and the wedge (1.10) does not exist; the paper's `γ = 0` remark (p. 25, "`ℍ` itself is
  invariant under horizontal translations") is informal. Disclosed pin.
* The field on `D` is given through its pairings `Ψ ω μ = (h, μ)` with measures carried by compact
  subsets of `D ∪ (a, b)` (circles in `D`, small semicircles centred in `(a, b)`): Gaussian with mean
  `∫ 𝔥₀ dμ` and covariance `∫∫ G_D dμ dν`, `G_D` the mixed Green's function (by reflection, see
  `mixedGreen`). The law is unconditional (`𝒢 = ⊥`). Arc averages are regular where defined.
* `μ ω` is the quantum area (1.1) of `h` on `D`, `ν ω` the quantum boundary length (1.2) on `(a, b)`;
  `ν_h[a, b] = ν_h((a, b))` (no atoms).
* Adding `C/γ` multiplies area by `e^C`; translating by `−x` pushes `μ` forward by `z ↦ z − x`; the
  surface `S_{h*+C/γ}` is represented by its canonical description (p. 21), whose area measure is
  `canonicalMeasure (e^C · (μ ω).map (· − x))`. As on p. 21, `μ` is zero outside `D − x`.
* Convergence in law for the topology of doubly marked quantum surfaces (convergence of the canonical
  `μ` on bounded sets, pp. 23–24) is stated as convergence of every finite-dimensional law
  `(∫ f_j dμ)_j`, `f_j` continuous with compact support, tested against bounded continuous `F`; for
  random measures this is convergence in law for the vague topology (Kallenberg, *Random Measures*,
  Thm 4.11). The left side is the expectation under the two-step sampling, written as
  `Z⁻¹ E[∫_{[a,b]} F(…) ν_h(dx)]` with `Z = E ν_h[a, b]`.
* The limit is the canonical description of any `γ`-quantum wedge realization `(Ω', P', W₁, W₂, Ψw)`
  (1.10) with area measure `μw`; the statement holds for every such realization. -/
theorem proposition_1_6 {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (D : Set ℂ) (c d : ℝ) (hD : IsSegmentDomain D c d)
    (Gstar : ℂ → ℂ → ℝ) (hG : IsDirichletGreen (reflectedDomain D c d) Gstar)
    (a b : ℝ) (hab : a < b) (hca : c ≤ a) (hbd : b ≤ d)
    (frakh0 : ℂ → ℝ) (hh0 : ContinuousOn frakh0 (D ∪ realSegment a b))
    (Ψ : Ω → Measure ℂ → ℝ)
    (hΨ_reg : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℂ × ℝ => arcAvg (Ψ ω) p.1 p.2)
      {p : ℂ × ℝ | 0 ≤ p.1.im ∧ 0 < p.2 ∧
        Metric.closedBall p.1 p.2 ∩ {w : ℂ | 0 ≤ w.im} ⊆ D ∪ realSegment a b})
    (hΨ : IsCondGaussianFieldOn P ⊥ Set.univ (IsAdmissibleIn D a b) Ψ
      (fun _ μ => ∫ z, frakh0 z ∂μ) (fun _ μ ν => kernelEnergy (mixedGreen Gstar) μ ν))
    (μ : Ω → Measure ℂ) (hμ : ∀ᵐ ω ∂P, IsAreaMeasureOn γ D (arcAvg (Ψ ω)) (μ ω))
    (ν : Ω → Measure ℝ)
    (hν : ∀ᵐ ω ∂P, IsBoundaryLengthOn γ (Set.Ioo a b) (fun x ε => arcAvg (Ψ ω) (x : ℂ) ε) (ν ω))
    (hfin : ∫⁻ ω, ν ω (Set.Icc a b) ∂P < ∞)
    (Ω' : Type v) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (W₁ W₂ : ℝ≥0 → Ω' → ℝ) (Ψw : Ω' → Measure ℂ → ℝ) (hw : IsWedgeField γ γ P' W₁ W₂ Ψw)
    (μw : Ω' → Measure ℂ) (hμw : ∀ᵐ ω' ∂P', IsAreaMeasureOn γ Hplane (arcAvg (Ψw ω')) (μw ω')) :
    ∀ (k : ℕ) (f : Fin k → ℂ → ℝ), (∀ j, Continuous (f j) ∧ HasCompactSupport (f j)) →
    ∀ F : (Fin k → ℝ) → ℝ, Continuous F → (∃ M : ℝ, ∀ y, |F y| ≤ M) →
      Tendsto (fun C : ℝ => (∫⁻ ω, ν ω (Set.Icc a b) ∂P).toReal⁻¹ *
          ∫ ω, ∫ x in Set.Icc a b,
            F (fun j => ∫ z, f j z ∂(canonicalMeasure
              (ENNReal.ofReal (Real.exp C) • (μ ω).map (fun z => z - (x : ℂ))))) ∂(ν ω) ∂P)
        atTop
        (𝓝 (∫ ω', F (fun j => ∫ z, f j z ∂(canonicalMeasure (μw ω'))) ∂P')) := by sorry

end QuantumZipper.Welding
