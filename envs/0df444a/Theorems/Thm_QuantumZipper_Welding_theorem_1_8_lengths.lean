-- Prove2me | Theorems.Thm_QuantumZipper_Welding_theorem_1_8_lengths
-- name    : QuantumZipper.Welding.theorem_1_8_lengths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:57.580356+00:00
-- url     : https://prove2.me/theorems/2b2a78ac-8318-42ae-b6db-f2dd6062a633
-- title:
--   Theorem 1.8 (length clause) — on an SLE-decorated $(\gamma-2/\gamma)$-wedge the two sides of $\eta$ have equal quantum length
-- statement:
--   Fix $\gamma\in(0,2)$ and $\kappa=\gamma^2$. Let $\mathcal S$ be a $(\gamma-2/\gamma)$-quantum wedge with field $h$, and let $\eta$ be a chordal $\mathrm{SLE}_\kappa$ in $\mathbb H$ from $0$ to $\infty$, independent of $h$. Fix $t>0$. Unzip $\eta([0,t])$ by the centred forward Loewner map $f^\eta_t=g_t-U_t$, with inverse $\psi_t(u)=F_t(u+U_t)$, and transform the field by (1.3):
--   $$h^t=h\circ\psi_t+Q\log|\psi_t'|.$$
--   Let $x_-<0<x_+$ be the real points with $\psi_t(x_\pm)=0$. Then almost surely
--   $$\nu_{h^t}\big([x_-,0]\big)=\nu_{h^t}\big([0,x_+]\big).$$
--   That is, the quantum lengths of the left and right sides of $\eta([0,t])$ agree.
--
--   This is the clause of Theorem 1.8 ("their quantum boundary lengths along $\eta$ agree") that the proof of Theorem 1.3 transfers to the reverse-SLE setting by absolute continuity.
--
--   **Formalization Note** The other clauses of Theorem 1.8 are not formalized in this mission: the two sides being independent $\gamma$-wedges, and zipper stationarity. The forward SLE and its Loewner maps are the platform's `OAI.SLEExactGauge.IsOrdinaryChordalSLE` and `IsCapacityTwoWitness`, with $\partial_tg_t=2/(g_t-U_t)$ and $z(g_t(z)-z)\to2t$. The wedge field is the representation (1.10) with $\alpha=\gamma-2/\gamma<Q$; given $(A,\eta)$, $h^t$ is Gaussian with mean $\int(m_A\circ\psi_t+Q\log|\psi_t'|)\,d\mu$ and covariance $\iint G^\dagger(\psi_tu,\psi_tv)$. The paper uses the canonical description. Equal side lengths are invariant under the joint rescaling (1.8) of field and curve, and $\mathrm{SLE}_\kappa$ is scale invariant, so the two representatives give equivalent statements. The points $x_\pm$ are encoded by radial boundary limits. The claim is stated for each fixed $t$, almost surely.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Theorem 1.8 (wedge decomposition, last clause), p. 26; unzipping convention p. 56; use in the proof of Theorem 1.3, p. 71

import Mathlib
import Definitions.Def_SLELowerPositivity
import Definitions.Def_QuantumZipper_Welding_Setting
import Definitions.Def_QuantumZipper_Welding_QuantumLength
import Definitions.Def_QuantumZipper_Welding_Wedge

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper.Welding

/-- **Theorem 1.8, wedge decomposition: the boundary-length clause** (Sheffield, Conformal weldings
of random surfaces, arXiv:1012.4797v2, Theorem 1.8, p. 26). Fix `γ ∈ (0, 2)`, `κ = γ²`. Let `S` be a
`(γ − 2/γ)`-quantum wedge with field `h`, and let `η` be a chordal `SLE_κ` in `ℍ` from `0` to `∞`,
independent of `h`. Then the quantum boundary lengths of the two sides of `η` agree: for every
`t > 0`, unzip `η([0, t])` by the centred forward Loewner map `f^η_t = g_t − U_t` and transform the
field by (1.3); the quantum length (1.2) of the image `[x₋, 0]` of the left side of `η([0, t])`
equals that of the image `[0, x₊]` of its right side.

**Formalization Note**
* Only the clause "their quantum boundary lengths along `η` agree" of Theorem 1.8 is formalized here
  (the clause used in the proof of Theorem 1.3, p. 71); the independence of the two `γ`-wedges and
  the zipper-stationarity items 1–3 are not stated in this mission.
* Lengths along `η` are "well defined by unzipping" (p. 26; p. 56: "to measure the `ν_h` length
  along the left side of `η([0, t])`, we may 'unzip' via `f^η_t` — and the transformation rule
  (1.3)"). With `ψ_t(u) = F_t(u + U_t)` the inverse of `f^η_t` (from the capacity-two witness
  `(G, F)` of the trace `η`, platform definition `OAI.SLEExactGauge.IsCapacityTwoWitness`), the
  unzipped field is `h ∘ ψ_t + Q log |ψ_t′|`. The real points `x₋ < 0 < x₊` with `ψ_t(x_± + i0) = 0`
  (radial limits) bound the images of the two sides.
* The wedge field is `h = h† + Q(−log |·|) + A_{−log |·|}` (1.10) with `α = γ − 2/γ < Q`, `A` built
  from independent Brownian motions `W₁`, `W₂`, `h†` independent of `(A, η)`. So, given
  `σ(W₁, W₂, η)`, the unzipped field's pairings are Gaussian with mean
  `∫ (m_A(ψ_t u) + Q log |ψ_t′(u)|) μ(du)` and covariance `∫∫ G†(ψ_t u, ψ_t v)`; `Ψ` is that field.
* **Representative.** The paper's `h` is the canonical description (`µ_h(B₁(0)) = 1`); the field
  here is the representative (1.10) with `inf {t : A_t = 0} = 0`. Equality of the two side lengths is
  invariant under the coordinate change (1.8) applied jointly to the field and the curve, and the
  law of `SLE_κ` is scale invariant, so the statement for one representative (with `η` independent of
  it) is equivalent to the statement for the other. Disclosed reading.
* The statement is made for each fixed `t > 0`, almost surely (both sides are monotone and
  continuous in `t`, so this is equivalent to "almost surely for all `t`" for a joint version).
* `(γ − 2γ)` on p. 70 is a misprint for `(γ − 2/γ)`. -/
theorem theorem_1_8_lengths {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (W₁ W₂ : ℝ≥0 → Ω → ℝ) (hW₁ : IsBrownianReal W₁ P) (hW₂ : IsBrownianReal W₂ P)
    (hW : IndepFun (fun ω t => W₁ t ω) (fun ω t => W₂ t ω) P)
    (η : Ω → ℝ≥0 → ℂ) (hη : OAI.SLEExactGauge.IsOrdinaryChordalSLE (γ ^ 2) η P)
    (hηW : IndepFun (fun ω => ((fun t => W₁ t ω), (fun t => W₂ t ω))) η P)
    (U : Ω → ℝ≥0 → ℝ) (Gm Fm : Ω → ℝ≥0 → ℂ → ℂ)
    (hwit : ∀ᵐ ω ∂P, OAI.SLEExactGauge.IsCapacityTwoWitness (U ω) (η ω) (Gm ω) (Fm ω))
    (hU_meas : ∀ t : ℝ≥0, Measurable fun ω => U ω t)
    (hF_meas : ∀ (t : ℝ≥0) (z : ℂ), Measurable fun ω => Fm ω t z)
    (t : ℝ≥0) (ht : 0 < t)
    (Ψ : Ω → Measure ℂ → ℝ) (hΨ_reg : ∀ᵐ ω ∂P, IsRegularArcField (Ψ ω))
    (hΨ : IsCondGaussianFieldOn P
      (pathSigma W₁ ⊔ pathSigma W₂ ⊔ MeasurableSpace.comap η inferInstance) Set.univ
      IsAdmissible Ψ
      (fun ω μ => ∫ u, (wedgeMean (γ - 2 / γ) (Qc γ) (fun s => W₁ s ω) (fun s => W₂ s ω)
          (Fm ω t (u + (U ω t : ℂ))) +
          Qc γ * Real.log ‖deriv (Fm ω t) (u + (U ω t : ℂ))‖) ∂μ)
      (fun ω μ ν => kernelEnergy
        (fun u v => lateralGreen (Fm ω t (u + (U ω t : ℂ))) (Fm ω t (v + (U ω t : ℂ)))) μ ν))
    (ν : Ω → Measure ℝ)
    (hν : ∀ᵐ ω ∂P, IsBoundaryLengthOn γ Set.univ (fun x ε => arcAvg (Ψ ω) (x : ℂ) ε) (ν ω)) :
    ∀ᵐ ω ∂P, ∀ xm xp : ℝ, xm < 0 → 0 < xp →
      Tendsto (fun y : ℝ => Fm ω t ((xm : ℂ) + (U ω t : ℂ) + (y : ℂ) * Complex.I))
        (𝓝[>] 0) (𝓝 0) →
      Tendsto (fun y : ℝ => Fm ω t ((xp : ℂ) + (U ω t : ℂ) + (y : ℂ) * Complex.I))
        (𝓝[>] 0) (𝓝 0) →
      ν ω (Set.Icc xm 0) = ν ω (Set.Icc 0 xp) := by sorry

end QuantumZipper.Welding
