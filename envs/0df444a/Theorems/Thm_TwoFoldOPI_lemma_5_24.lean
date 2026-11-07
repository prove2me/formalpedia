-- Prove2me | Theorems.Thm_TwoFoldOPI_lemma_5_24
-- name    : TwoFoldOPI.lemma_5_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:43:55.765498+00:00
-- url     : https://prove2.me/theorems/30f95f9d-b30f-438a-9c1b-074bb5059823
-- title:
--   Lemma 5.24 — approximation under postselection
-- statement:
--   Let $\rho_0$ (ideal input) and $\rho_1$ (actual input) be density matrices with trace distance $D(\rho_0,\rho_1)=\tfrac12\|\rho_0-\rho_1\|_1\le\delta$. Apply to both the same quantum operation with a success flag: completely positive linear maps $\Phi_s$ (success) and $\Phi_f$ (failure) with $\Phi_s+\Phi_f$ trace preserving. Let
--   $$p=\operatorname{tr}\Phi_s(\rho_0),\qquad p'=\operatorname{tr}\Phi_s(\rho_1).$$
--   If $p>\delta$, then
--   1. $p'\ge p-\delta$, and
--   2. the states conditioned on success are close:
--   $$D\Big(\frac{\Phi_s(\rho_0)}{p},\frac{\Phi_s(\rho_1)}{p'}\Big)\le\frac{\delta}{p-\delta}.$$
--
--   This bounds how errors in a prepared input propagate through a postselected step; it is used in the proof of Theorem 5.30 to control the trial's conditioned state.
--
--   Differences from the source:
--   - reading: the same quantum operation, which also outputs a success flag → two linear completely positive maps Φ_s, Φ_f (success, failure branches) whose sum is trace-preserving; success probability tr Φ_s(ρ), conditioned state Φ_s(ρ)/tr Φ_s(ρ); reason: a quantum operation with a classical success flag is exactly a two-outcome instrument
--   - encoding: input states; trace distance D(σ, τ) = ½‖σ − τ‖₁ (p.26) → density matrices (PSD, trace 1); QAlgorithms.traceDistance = ½ traceNorm; reason: the paper's convention, same instances
--   - reading: closing remark "The same argument applies when δ also includes circuit-approximation errors before the success test" → not stated; reason: a remark on the proof's reach, not part of the lemma's claim
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Lemma 5.24, p. 26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity

open scoped Matrix ComplexOrder

namespace TwoFoldOPI

/-- **Lemma 5.24 (Approximation under postselection).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Lemma 5.24, p.26: "Suppose an ideal input state and an actual input state have trace
distance at most δ, and apply to both the same quantum operation, which also outputs a success
flag. If the success probability on the ideal input is p > δ, then the success probability on the
actual input is at least p−δ, and the two normalized states conditioned on success have trace
distance at most δ/(p −δ)."

**Formalization Note.** A quantum operation with a success flag is a pair of linear completely
positive maps `Φ_s, Φ_f` (success and failure branches) whose sum is trace-preserving, i.e. a
two-outcome instrument. On a state `ρ` the success probability is `tr Φ_s(ρ)` and the state
conditioned on success is `Φ_s(ρ)/tr Φ_s(ρ)`. States are density matrices (positive semidefinite,
trace `1`). Trace distance is `½‖·‖₁` (`QAlgorithms.traceDistance`), the paper's convention
`D(σ, τ) = ½‖σ − τ‖₁` (p.26). The page's last sentence ("The same argument applies when δ also
includes circuit-approximation errors before the success test") is a remark and is not stated. -/
theorem lemma_5_24 {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (ρ₀ ρ₁ : Matrix ι ι ℂ) (hρ₀ : ρ₀.PosSemidef ∧ ρ₀.trace = 1)
    (hρ₁ : ρ₁.PosSemidef ∧ ρ₁.trace = 1) (δ : ℝ)
    (hδ : QAlgorithms.traceDistance ρ₀ ρ₁ ≤ δ)
    (Φs Φf : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (hs : QAlgorithms.Entanglement.IsCompletelyPositive Φs)
    (hf : QAlgorithms.Entanglement.IsCompletelyPositive Φf)
    (htp : ∀ X : Matrix ι ι ℂ, (Φs X + Φf X).trace = X.trace)
    (hp : δ < (Φs ρ₀).trace.re) :
    (Φs ρ₀).trace.re - δ ≤ (Φs ρ₁).trace.re ∧
      QAlgorithms.traceDistance (((Φs ρ₀).trace.re : ℂ)⁻¹ • Φs ρ₀)
          (((Φs ρ₁).trace.re : ℂ)⁻¹ • Φs ρ₁) ≤
        δ / ((Φs ρ₀).trace.re - δ) := by sorry

end TwoFoldOPI
