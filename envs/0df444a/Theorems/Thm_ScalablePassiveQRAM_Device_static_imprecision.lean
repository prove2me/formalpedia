-- Prove2me | Theorems.Thm_ScalablePassiveQRAM_Device_static_imprecision
-- name    : ScalablePassiveQRAM.Device.static_imprecision
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:23.539807+00:00
-- url     : https://prove2.me/theorems/c990d2b1-adc7-41e2-9785-80f130137e44
-- title:
--   Corollary 10 — Repeated queries with static imprecision
-- statement:
--   Prepare vacant auxiliaries and memory $|D\rangle$ once, use the recorded interface with ideal root controls, and permit arbitrary Hermitian static error terms on arbitrary supports, including the memory and root record. For every $n\ge1$, $\Omega>0$, $\Delta$, and algorithm with $m\ge1$ queries,
--
--   $$\epsilon_m\le\min\{2,2m(m+1)\tau W\},\qquad W\le(F_n+3n+3)\lambda_{\rm err}.$$
--
--   Here $\tau=\pi/\Omega$. For every $\Omega_0>0$ (the constant in $\Omega=\Theta(1/L)$) there are constants $C,c>0$, depending only on $\Omega_0$, such that for every $n\ge1$, every $\Delta$, every $\Omega$ with $\Omega L\ge\Omega_0$, every error family and every algorithm with $m\ge1$ queries, $\epsilon_m\le Cm^2\lambda_{\rm err}\log^4N$, and the error is at most $\varepsilon$ when $\lambda_{\rm err}\le c\varepsilon/(m^2\log^4N)$. If at most $d\ge1$ error terms touch any qubit and each bound is at most $\delta$, then $\delta\le c\varepsilon/(m^2d\log^4N)$ suffices. The device is traced out here; the target is the original database even if perturbations change stored bits.
--
--   Differences from the source:
--   - encoding: one-based bit and transition indices and tensor-product register notation → zero-based finite index types and matrices on all physical bit configurations; reason: the finite types enumerate the same modes and every operation is lifted to the full tensor product
--   - reading: unload reverses the load and routing uses the values that can occur on a valid history → unload bits in decreasing order and explicit bit or star flavor sets at every route; reason: the source leaves this schedule implicit; this is the execution described in §§3.1–3.2 and reproduces the layer counts
--   - encoding: rectangular unhalved diamond norm of the explicitly constructed channels → the identical density-operator supremum over every finite reference dimension for explicit superoperators, using the published trace norm; reason: this avoids inserting substantive CPTP proofs into definitions; the physical maps are encoding, unitary evolution, partial trace, replacement, and decoding channels
--   - generalization: the O(m²λ_err log⁴N) form and the per-component threshold for the construction with Ω=Θ(1/L) → for every Ω₀>0, uniform C,c depending only on Ω₀, valid for every Ω with ΩL≥Ω₀ and every real Δ; reason: only the lower side of Θ(1/L) enters through τ=π/Ω, and the exact bound (74) holds for every Δ; any source family Ω=Θ(1/L) with any splitting is an instance
--   - encoding: the per-component fraction 1/d_err → d_err≥1 for that fraction; the exact W bound covers empty incidence; reason: division by zero is not a physical precision requirement
--   - generalization: positive on-site energy splitting Δ → any real Δ in the exact algebraic pinning and separation identities; reason: commutation, the common eigenvalue, and unitary phase identities are algebraic in Δ and specialize to every physical positive splitting
-- source:
--   Siddhartha Jain, Alexander Dalzell, Connor Hann, STOC 2027 submission #129 (October 2026), Corollary 10, p. 31. Canonical PDF SHA256 725dff5ab83fbe7e163da05440b75cc1d24f83804408cc139eb8954d2f8a076e.

import Definitions.Def_ScalablePassiveQRAM_Device_Energy
import Mathlib

open scoped BigOperators Matrix
set_option synthInstance.maxSize 10000
noncomputable section

namespace ScalablePassiveQRAM.Device
local instance static_imprecisionDecidable (p : Prop) : Decidable p := Classical.propDecidable p
local instance static_imprecisionDecidableEq (a : Type) : DecidableEq a := Classical.decEq a

theorem static_imprecision :
    (∀ (n : ℕ), 1 ≤ n → ∀ (Ω Δ : ℝ), 0 < Ω → ∀ (E : StaticErrors n),
      (∀ x : Address n, (extendedFootprint n x).card = footprintSize n+3*n+3) ∧
      branchWeight E ≤ (footprintSize n+3*n+3)*errorIncidence E ∧
      (∀ (m w : ℕ), 1 ≤ m → ∀ (D : Database n) (A : Algorithm n w m),
        staticError A E Ω Δ D ≤ min 2 (2*m*(m+1)*(Real.pi/Ω)*branchWeight E))) ∧
    (∀ Ω₀ : ℝ, 0 < Ω₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (Ω Δ : ℝ), Ω₀ ≤ Ω * (length n : ℝ) →
      ∀ (E : StaticErrors n) (m w : ℕ), 1 ≤ m → ∀ (D : Database n) (A : Algorithm n w m),
        staticError A E Ω Δ D ≤ C*m^2*errorIncidence E*(Real.log ((2:ℝ)^n))^4 ∧
        (∀ ε : ℝ, 0 < ε → errorIncidence E ≤ c*ε/(m^2*(Real.log ((2:ℝ)^n))^4) →
          staticError A E Ω Δ D ≤ ε) ∧
        (∀ (d : ℕ) (δ ε : ℝ), 1 ≤ d → 0 < ε →
          (∀ q : ExtendedQubit n, (Finset.univ.filter fun α => q ∈ E.support α).card ≤ d) →
          (∀ α, E.bound α ≤ δ) → δ ≤ c*ε/(m^2*d*(Real.log ((2:ℝ)^n))^4) →
          staticError A E Ω Δ D ≤ ε)) := by sorry

end ScalablePassiveQRAM.Device
