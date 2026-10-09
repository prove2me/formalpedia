-- Prove2me | Theorems.Thm_QuantumZipper_Welding_proposition_5_4
-- name    : QuantumZipper.Welding.proposition_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:17:57.826987+00:00
-- url     : https://prove2.me/theorems/400c3447-ff57-4244-92ee-f909b3f92d3a
-- title:
--   Proposition 5.4 — under $\Gamma_\rho\propto e^{(h^0,\rho)}\Gamma$ the zipper is the modified SLE of Theorem 4.5
-- statement:
--   Let $\rho=\rho_+-\rho_-$ be a signed measure on $\mathbb H$ with total mass zero and finite energy $(-\Delta^{-1}\rho,\rho)<\infty$. Let $\Gamma_\rho$ be the probability measure with $d\Gamma_\rho/d\Gamma\propto e^{(h^0,\rho)}$, where $\Gamma$ is the capacity zipper law of §5.2. Then:
--
--   1. under $\Gamma_\rho$, the zipping-up maps $(f_t)_{t\ge0}$ have the law of the modified SLE process of Theorem 4.5;
--   2. given $f_t$ for some $t\ge0$, the $\Gamma_\rho$-conditional law of $h^0$ is that of $\tilde h\circ f_t+\hat{\mathfrak h}_t$, with $\hat{\mathfrak h}_t$ as in (4.4).
--
--   The measure entering (4.4)–(4.6) is $\rho'=2\sqrt\kappa\,\rho$. Concretely, under $\Gamma_\rho$,
--   $$B'_t=B_t-\frac1{\sqrt\kappa}\int_0^t\!\!\int\operatorname{Re}\frac{-1}{f_s(y)}\,\rho'(dy)\,ds$$
--   is a standard Brownian motion, and $\hat{\mathfrak h}_t=\mathfrak h_t+\int G(f_t(y),f_t(\cdot))\,\rho(dy)$.
--
--   The proposition describes how the space–time stationary process of Proposition 5.3 evolves in capacity time.
--
--   **Formalization Note** Weighting by $e^{(h,\rho/(2\sqrt\kappa))}$ gives (4.6) with $\rho$ ((4.13), p. 54; the proof of Lemma 5.6, p. 68). The printed weight $e^{(h^0,\rho)}$ therefore gives Theorem 4.5's process for $2\sqrt\kappa\,\rho$, and this reading is pinned explicitly. Total mass zero ($\rho_+(\mathbb C)=\rho_-(\mathbb C)$) is the assumption of p. 63; it makes $(h^0,\rho)$ independent of the additive constant. $\rho_\pm$ are admissible (finite, bounded support, no mass outside $\mathbb H$, finite logarithmic energy); the support may accumulate at $\mathbb R$, as for the $\sigma_{x,\varepsilon}-\sigma_{0,1}$ the paper uses on p. 67. The conclusion also asserts that, $\Gamma_\rho$-a.s., the drift $s\mapsto\int\operatorname{Re}(-1/f_s(y))\,\rho'(dy)$ is locally integrable, so $B'$ is a genuine integral. $\Gamma$ is encoded by its restriction to $(h^0,(f_t)_{t\ge0})$, with $h^0_1(0)=0$.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, Proposition 5.4, p. 65 (with §4.2, (4.13), p. 54, and §5.3, p. 63)

import Mathlib
import Definitions.Def_QuantumZipper_Welding_Setting
import Definitions.Def_QuantumZipper_Welding_QuantumLength
import Definitions.Def_QuantumZipper_Welding_Zipper

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper.Welding

/-- **Proposition 5.4** (Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2,
Proposition 5.4, p. 65). Let `ρ = ρ₊ − ρ₋` be a signed measure on `ℍ` of total mass zero with finite
energy, and let `Γ_ρ` be the law with `dΓ_ρ/dΓ ∝ e^{(h⁰, ρ)}`. Then under `Γ_ρ` the zipping-up maps
`(f_t)_{t ≥ 0}` are the modified reverse SLE of Theorem 4.5, and given `f_t` the conditional law of
`h⁰` is that of `h̃ ∘ f_t + ĥ_t` ((4.4)), for the measure `2√κ·ρ` in (4.4)–(4.6).

**Formalization Note**
* `Γ` is encoded by `IsGammaZipper` (its restriction to `(h⁰, (f_t)_{t ≥ 0})`, §5.2), with the
  additive constant of `h⁰` fixed by `h₁(0) = 0`; `(h⁰, ρ) = Ψ(ρ₊) − Ψ(ρ₋)` does not depend on that
  constant because `ρ₊(ℂ) = ρ₋(ℂ)`.
* **Constant (disclosed reading).** Weighting by `e^{(h, ρ/(2√κ))}` produces the drift (4.6) with
  measure `ρ` and the shift (4.4) (§4.2, (4.13), p. 54; and the proof of Lemma 5.6, p. 68). Weighting
  by `e^{(h⁰, ρ)}`, as printed here, therefore gives "the modified SLE process in Theorem 4.5" for the
  measure `ρ' = 2√κ·ρ`: under `Γ_ρ`, `B'_t = B_t − (1/√κ) ∫₀ᵗ ∫ Re(−1/f_s(y)) ρ'(dy) ds` is a standard
  Brownian motion (so `W = √κ B' + ∫ (−Re f_s⁻¹, ρ') ds`, which is (4.6) for `ρ'`), and `ĥ_t` is (4.4)
  for `ρ'`, i.e. `ĥ_t = 𝔥_t + ∫ G_t(y, ·) ρ(dy)`.
* "Total integral zero" (`ρ₊(ℂ) = ρ₋(ℂ)`) is needed for `(h⁰, ρ)` to be defined for `h⁰` modulo
  constants (p. 63: "we assume that `ρ` has total integral zero"); disclosed pin.
* "Signed measure on `ℍ` with `(−Δ⁻¹ρ, ρ) < ∞`" is taken as: `ρ₊`, `ρ₋` admissible (finite, bounded
  support, no mass outside `ℍ`, finite logarithmic energy), which gives finite energy. The support may
  accumulate at `ℝ` (the paper applies this proposition to `σ_{x,ε} − σ_{0,1}`, p. 67).
* The drift of (4.6) is part of the conclusion: `Γ_ρ`-a.s. `s ↦ ∫ Re(−1/f_s(y)) ρ'(dy)` is locally
  integrable, so `B'` below is a genuine integral and not a junk value.
* No stopping time is needed: `ρ` charges only `ℍ`, where `f_t ≠ 0`. -/
theorem proposition_5_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ)
    (B : ℝ≥0 → Ω → ℝ) (g : Ω → ℝ≥0 → ℂ → ℂ) (Ψ : Ω → Measure ℂ → ℝ)
    (hΓ : IsGammaZipper κ P B g Ψ)
    (ρp ρn : Measure ℂ) (hρp : IsAdmissible ρp) (hρn : IsAdmissible ρn)
    (hmass : ρp Set.univ = ρn Set.univ) :
    let Q : Measure Ω := tilt P (fun ω => ENNReal.ofReal (Real.exp (Ψ ω ρp - Ψ ω ρn)))
    let ρp' : Measure ℂ := ENNReal.ofReal (2 * Real.sqrt κ) • ρp
    let ρn' : Measure ℂ := ENNReal.ofReal (2 * Real.sqrt κ) • ρn
    (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, IntervalIntegrable
        (fun s : ℝ => drift (bmDrive κ B ω) (g ω) ρp' ρn' (Real.toNNReal s)) volume 0 (t : ℝ)) ∧
    IsBrownianReal (fun t ω => B t ω - 1 / Real.sqrt κ *
        ∫ s in (0 : ℝ)..(t : ℝ), drift (bmDrive κ B ω) (g ω) ρp' ρn' (Real.toNNReal s)) Q ∧
      ∀ t : ℝ≥0, IsCondGaussianFieldOn Q (natSigma B t) Set.univ IsAdmissible Ψ
        (fun ω μ => normMean (hatH κ (bmDrive κ B ω) (g ω) ρp' ρn' t) μ)
        (fun ω μ ν => normCov (revCov (bmDrive κ B ω) (g ω) t) μ ν) := by sorry

end QuantumZipper.Welding
