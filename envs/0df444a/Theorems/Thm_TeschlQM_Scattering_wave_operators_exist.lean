-- Prove2me | Theorems.Thm_TeschlQM_Scattering_wave_operators_exist
-- name    : TeschlQM.Scattering.wave_operators_exist
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T10:34:24.439362+00:00
-- url     : https://prove2.me/theorems/6bc708e9-fbe9-4958-a93e-3a5c20769237
-- title:
--   Theorem 12.4 — for V ∈ L²(ℝ³) the wave operators of H₀ + V exist and 𝔇(Ω±) = ℌ
-- statement:
--   Let $H_0 = -\Delta$ be the free Schrödinger operator on $\mathfrak H = L^2(\mathbb R^3)$ with domain $H^2(\mathbb R^3)$, let $V \in L^2(\mathbb R^3)$ be real, and let $H = H_0 + V$ with $\mathfrak D(H) = H^2(\mathbb R^3)$. Then the wave operators exist:
--   $$\mathfrak D(\Omega_+) = \mathfrak D(\Omega_-) = \mathfrak H, \qquad\text{i.e. } \lim_{t\to\pm\infty}\mathrm e^{\mathrm itH}\mathrm e^{-\mathrm itH_0}\psi \text{ exists for every } \psi \in L^2(\mathbb R^3).$$
--   This is the first existence result for wave operators of Schrödinger operators: every free motion is the asymptote, at $t \to +\infty$ and at $t \to -\infty$, of a motion under the potential.
--
--   **Formalization Note.** $L^2(\mathbb R^3)$ is `Lp ℂ 2` on `EuclideanSpace ℝ (Fin 3)`; $V$ is a real function with `MemLp V 2`. $H_0$ and $H$ are `LinearPMap`s characterized by `IsFreeSchrodinger 3 H₀` (Mathlib's $L^2$ Fourier transform, constants translated: $\mathcal F_M(H_0\psi)(\xi) = 4\pi^2|\xi|^2\mathcal F_M\psi(\xi)$) and `IsSchrodingerOp 3 H₀ V H`. The projection-valued measures $P_0$ of $H_0$ and $P$ of $H$ are taken as data with $H_0 = \int\lambda\,dP_0$, $H = \int\lambda\,dP$ (Theorems 3.7, 7.8, 10.2 guarantee them); nothing is assumed about $\Omega_\pm$. The conclusion is that the limit exists for every $\psi$, for both signs `s : ℤˣ`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 249, Theorem 12.4

import Mathlib
import Definitions.Def_TeschlQM_Shared_IsProjValuedMeasure
import Definitions.Def_TeschlQM_Shared_IsSpectralIntegral
import Definitions.Def_TeschlQM_Scattering_waveOperator
import Definitions.Def_TeschlQM_Scattering_freeSchrodinger

open MeasureTheory

namespace TeschlQM.Scattering

/-- Teschl, p. 249, Theorem 12.4: let `H₀` be the free Schrödinger operator on `L²(ℝ³)` and
`H = H₀ + V` with a real potential `V ∈ L²(ℝ³)`. Then the wave operators `Ω₊` and `Ω₋` exist:
`𝔇(Ω_±) = ℌ = L²(ℝ³)`, i.e. `lim_{t→±∞} e^{itH} e^{−itH₀} ψ` exists for every `ψ`.
The projection-valued measures `P₀` of `H₀` and `P` of `H` are taken as data
(`H₀ = ∫ λ dP₀`, `H = ∫ λ dP`); `s = ±1` is the sign of `Ω_±`. -/
theorem wave_operators_exist (V : EuclideanSpace ℝ (Fin 3) → ℝ) (hV : MemLp V 2 volume)
    (H₀ H : L2 3 →ₗ.[ℂ] L2 3) (hH₀ : IsFreeSchrodinger 3 H₀) (hH : IsSchrodingerOp 3 H₀ V H)
    (P₀ P : Set ℝ → (L2 3 →L[ℂ] L2 3))
    (hP₀ : TeschlQM.Shared.IsProjValuedMeasure P₀) (hP₀H₀ : TeschlQM.Shared.IsSpectralIntegral P₀ (fun x : ℝ => (x : ℂ)) H₀)
    (hP : TeschlQM.Shared.IsProjValuedMeasure P) (hPH : TeschlQM.Shared.IsSpectralIntegral P (fun x : ℝ => (x : ℂ)) H) :
    ∀ s : ℤˣ, waveDomain P₀ P s = Set.univ := by sorry

end TeschlQM.Scattering
