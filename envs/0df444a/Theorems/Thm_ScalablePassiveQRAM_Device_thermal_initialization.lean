-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_thermal_initialization
-- name    : ScalablePassiveQRAM.Device.thermal_initialization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:56:08.488599+00:00
-- url     : https://prove2.me/theorems/def81bf8-eadc-44ce-a83c-0ccb6b0a320f
-- title:
--   Theorem 8 — Thermal initialization
-- statement:
--   Let $n\ge1$, $\Omega>0$, and $g=\Delta-\kappa>0$. Fix $D$ and prepare the interacting Gibbs marginal $\rho_{\beta,D}$ once, for any real inverse temperature $\beta$. For any algorithm with $m\ge1$ queries, any finite workspace, and arbitrary channels on its registers between queries, keep the device in the output. Then
--
--   $$\|\mathcal A^{\rm phys}_{m,D}-[\eta\mapsto\mathcal A^{\rm ideal}_{m,D}(\eta)\otimes\rho_{\beta,D}]\|_\diamond\le\min\{2,4m\sqrt{F_ne^{-\beta g}}\}.$$
--
--   For $\varepsilon>0$, equation (65), $\beta g\ge\log F_n+2\log(4m/\varepsilon)$, suffices. Explicitly, for all $A,a,b\ge0$ and $g_0>0$ there is $c>0$, uniform in the device and algorithm, such that for $n\ge2$, $m\le An^a$, $\varepsilon^{-1}\le An^b$, $0<\varepsilon<1$, and $g\ge g_0$, a temperature $0<T\le c/\log n$ suffices. There is no bulk reset between queries.
--
--   Differences from the source:
--   - encoding: one-based bit and transition indices and tensor-product register notation → zero-based finite index types and matrices on all physical bit configurations; reason: the finite types enumerate the same modes and every operation is lifted to the full tensor product
--   - reading: unload reverses the load and routing uses the values that can occur on a valid history → unload bits in decreasing order and explicit bit or star flavor sets at every route; reason: the source leaves this schedule implicit; this is the execution described in §§3.1–3.2 and reproduces the layer counts
--   - encoding: rectangular unhalved diamond norm of the explicitly constructed channels → the identical density-operator supremum over every finite reference dimension for explicit superoperators, using the published trace norm; reason: this avoids inserting substantive CPTP proofs into definitions; the physical maps are encoding, unitary evolution, partial trace, replacement, and decoding channels
--   - encoding: asymptotic log log N bounds → n≥2 for log log N formulas, with exact bounds also stated for n=1; reason: log log 2 is negative; these are asymptotic statements and the finite-size guarantees are kept without narrowing
--   - reading: the final sentence says this requires a temperature O(1/log n) → a uniform sufficient temperature condition; reason: equation (65) is a sufficient condition; necessity is not asserted by the source estimate
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Theorem 8, p. 29. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance thermal_initializationDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance thermal_initializationDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

theorem thermal_initialization :
    (∀ (n : ℕ), 1 ≤ n → ∀ (Ω Δ β : ℝ), 0 < Ω → 0 < Δ-kappa n Ω →
      ∀ (D : Database n) (m w : ℕ), 1 ≤ m → ∀ A : Algorithm n w m,
        thermalError A Ω Δ β D ≤ min 2 (4*m*Real.sqrt (footprintSize n * Real.exp (-β*(Δ-kappa n Ω)))) ∧
        (∀ ε : ℝ, 0 < ε → β*(Δ-kappa n Ω) ≥ Real.log (footprintSize n) + 2*Real.log (4*m/ε) →
          thermalError A Ω Δ β D ≤ ε)) ∧
    (∀ (A a b g₀ : ℝ), 0 ≤ A → 0 ≤ a → 0 ≤ b → 0 < g₀ →
      ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (m w : ℕ), 1 ≤ m →
        ∀ (ε T Ω Δ : ℝ), 0 < ε → ε < 1 → 0 < T → 0 < Ω →
          (m:ℝ) ≤ A*(n:ℝ)^a → ε⁻¹ ≤ A*(n:ℝ)^b → g₀ ≤ Δ-kappa n Ω →
          T ≤ c/Real.log n → ∀ (D : Database n) (alg : Algorithm n w m),
            thermalError alg Ω Δ (T⁻¹) D ≤ ε) := by sorry

end ScalablePassiveQRAM.Device
