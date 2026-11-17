-- Prove2me | Theorems.Thm_SpectralFeedback_Supplement_theorem_D_2_spectral_modulus
-- name    : SpectralFeedback.Supplement.theorem_D_2_spectral_modulus
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:58:44.361343+00:00
-- url     : https://prove2.me/theorems/b2090016-38f6-4a01-97ee-49d93a30a389
-- title:
--   Theorem D.2 — dimension-free spectral modulus: $0\le G(\rho)-G(\sigma)\le2\sqrt{T_0\tau}+\tau$
-- statement:
--   Let $m,r\ge1$ and extend $G_{m,r}$ to all positive matrices by (C.6), without trace normalization.
--
--   1. If $0\preceq\sigma\preceq\rho$ are complex $d\times d$ matrices, $T_0=\operatorname{tr}\rho$ and $\tau=\operatorname{tr}(\rho-\sigma)$, then
--   $$
--   0\le G_{m,r}(\rho)-G_{m,r}(\sigma)\le2\sqrt{T_0\tau}+\tau.\qquad\text{(D.10)}
--   $$
--   2. For probability vectors $\lambda,\nu\in\mathbb R^n$ with $\delta=\|\lambda-\nu\|_1$, writing $G_{m,r}(\lambda)$ for $G_{m,r}(\operatorname{diag}\lambda)$,
--   $$
--   |G_{m,r}(\lambda)-G_{m,r}(\nu)|\le\sqrt{2\delta}+\delta/2.\qquad\text{(D.11)}
--   $$
--
--   In both parts the maxima defining the values exist. The modulus does not depend on the dimension, which is what makes certified value enclosures possible from approximate spectra.
--
--   Differences from the source:
--   - generalization: probability spectra λ, ν → any probability vectors λ, ν ∈ ℝ^n (not required to be sorted), G evaluated at diag λ; reason: G is invariant under unitary conjugation, so sorted vectors are the special case; the source's argument (the common lower bound diag(min(λ_i, ν_i))) covers unsorted vectors
--   - encoding: the value G_{m,r}(ρ) (a maximum, (C.6)) → IsGreatest of the published rewardSet with F = χ_r; reason: the base mission's convention; IsGreatest asserts the maximum exists and equals the value, never a junk sSup
--   - encoding: 0 ⪯ σ ⪯ ρ, T_0 = tr ρ, τ = tr(ρ − σ) → σ ⪰ 0 and ρ − σ ⪰ 0; traces are real parts of the complex traces; reason: the traces of Hermitian matrices are real
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Theorem D.2, (D.10)–(D.11), p.55 (PDF p.57)

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_Supplement_chi

open scoped ComplexOrder

namespace SpectralFeedback

namespace Supplement

/-- **Theorem D.2** (A dimension-free spectral modulus; Qi, *Spectral Structure and Exact Arithmetic
of Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), p.55 (PDF p.57)). Extend
`G_{m,r}` to positive matrices by (C.6). If `0 ⪯ σ ⪯ ρ`, `T_0 = tr ρ` and `τ = tr(ρ − σ)`, then
`0 ≤ G_{m,r}(ρ) − G_{m,r}(σ) ≤ 2√(T_0 τ) + τ` (D.10). For probability spectra with
`δ = ‖λ − ν‖_1`, `|G_{m,r}(λ) − G_{m,r}(ν)| ≤ √(2δ) + δ/2` (D.11).

**Formalization Note** `G_{m,r}(·) = v` is `IsGreatest (rewardSet r (chi r) m ·) v`; each claim
asserts that the maxima exist and satisfy the bound. `0 ⪯ σ ⪯ ρ` is `σ ⪰ 0` and `ρ − σ ⪰ 0` (same
dimension `d`, any `d`, no trace normalization); traces are real parts of the complex traces.
`G_{m,r}(λ)` for a probability vector `λ ∈ ℝ^n` is `G_{m,r}(diag λ)`. The vectors `λ, ν` are any
probability vectors of the same length (not required to be sorted). -/
theorem theorem_D_2_spectral_modulus (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) :
    (∀ {d : ℕ} (ρ σ : Matrix (Fin d) (Fin d) ℂ), σ.PosSemidef → (ρ - σ).PosSemidef →
      ∃ v w : ℝ, IsGreatest (rewardSet r (chi r) m ρ) v ∧ IsGreatest (rewardSet r (chi r) m σ) w ∧
        0 ≤ v - w ∧
        v - w ≤ 2 * Real.sqrt (ρ.trace.re * (ρ - σ).trace.re) + (ρ - σ).trace.re) ∧
    (∀ {n : ℕ} (lam nu : Fin n → ℝ), 0 ≤ lam → ∑ i, lam i = 1 → 0 ≤ nu → ∑ i, nu i = 1 →
      ∃ v w : ℝ,
        IsGreatest (rewardSet r (chi r) m (Matrix.diagonal (fun i => ((lam i : ℝ) : ℂ)))) v ∧
        IsGreatest (rewardSet r (chi r) m (Matrix.diagonal (fun i => ((nu i : ℝ) : ℂ)))) w ∧
        |v - w| ≤ Real.sqrt (2 * ∑ i, |lam i - nu i|) + (∑ i, |lam i - nu i|) / 2) := by sorry

end Supplement

end SpectralFeedback
