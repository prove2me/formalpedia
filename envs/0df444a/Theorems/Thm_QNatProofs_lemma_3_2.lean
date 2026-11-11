-- Prove2me | Theorems.Thm_QNatProofs_lemma_3_2
-- name    : QNatProofs.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:00:52.794567+00:00
-- url     : https://prove2.me/theorems/d1a92989-aae0-4dd0-9c22-14175e510460
-- title:
--   Lemma 3.2 — Haar amplitudes avoid truncation boundaries
-- statement:
--   Let $|\phi\rangle=\sum_x|\phi_x|e^{i2\pi\theta_x}|x\rangle\sim\mathrm{Haar}_n$ with $N=2^n\ge2$, and let
--   $$
--   B_{T,\mathrm{mag}}=\{z\in\mathbb C:|z|=j2^{-T},\ j\in\{1,\dots,2^T\}\},\qquad B_{T,\mathrm{phase}}=\{re^{i2\pi j/2^T}:r\ge0,\ j\in\{0,\dots,2^T-1\}\}
--   $$
--   be the $T$-bit truncation boundaries of magnitude and phase, $B_T=B_{T,\mathrm{mag}}\cup B_{T,\mathrm{phase}}$. There is a universal constant $C$ such that for every $n\ge1$, every $T$ and every $\rho\ge0$,
--   $$
--   \Pr\big[\exists x:\ \mathrm{dist}(\phi_x,B_T)\le\rho\big]\le C\,N^{3/2}2^T\rho .
--   $$
--
--   So a Haar-random state's amplitude list does not change under a small perturbation, except with small probability; this is the key input to Theorem 3.1.
--
--   Differences from the source:
--   - encoding: O(N^{3/2}2^Tρ) → one constant C chosen before n, T and ρ; reason: the meaning of O(·) for a bound uniform in every parameter
--   - encoding: N = 2^n ≥ 2; dist(ϕ_x, B_T); j ∈ [2^T] → 1 ≤ n; Metric.infDist; 1 ≤ j ≤ 2^T; reason: Lean convention; same instances
--   - encoding: Haar_n, the Haar probability measure on the unit sphere of ℂ^{2^n} → the surface measure toSphere of an additive Haar measure on EuclideanSpace ℂ (Qubits n), normalized to mass 1; reason: the unique rotation-invariant probability measure on the sphere; same measure
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Lemma 3.2, p.12; proof p.13

import Mathlib
import Definitions.Def_QNatProofs_haar

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms MeasureTheory

/-- **Lemma 3.2 (Haar amplitudes avoid truncation boundaries)** (Li, Parham, *Natural proofs for
quantum state preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.12):
for `|ϕ⟩ ∼ Haar_n` with `N = 2ⁿ ≥ 2` and the `T`-bit truncation boundaries
`B_{T,mag} = {z ∈ ℂ : |z| = j 2^{-T}, j ∈ [2^T]}`,
`B_{T,phase} = {r e^{i2πj/2^T} : r ≥ 0, j ∈ {0, 1, …, 2^T − 1}}`, `B_T = B_{T,mag} ∪ B_{T,phase}`,
for every `ρ ≥ 0`, `Pr[∃ x : dist(ϕ_x, B_T) ≤ ρ] ≤ O(N^{3/2} 2^T ρ)`.

**Formalization Note** `O(·)` is one constant `C`, chosen before `n`, `T` and `ρ`; `[2^T]` is
`{1, …, 2^T}`; the distance to `B_T` is `Metric.infDist`. -/
theorem lemma_3_2 : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ (T : ℕ) (ρ : ℝ), 0 ≤ ρ →
    haar n {ϕ | ∃ x : Qubits n,
      Metric.infDist ((ϕ : EuclideanSpace ℂ (Qubits n)) x)
        ({z : ℂ | ∃ j : ℕ, 1 ≤ j ∧ j ≤ 2 ^ T ∧ ‖z‖ = (j : ℝ) * (2 : ℝ)⁻¹ ^ T} ∪
          {z : ℂ | ∃ r : ℝ, 0 ≤ r ∧ ∃ j : ℕ, j < 2 ^ T ∧
            z = (r : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) / (2 : ℂ) ^ T))}) ≤ ρ} ≤
      ENNReal.ofReal (C * ((2 : ℝ) ^ n) ^ ((3 : ℝ) / 2) * (2 : ℝ) ^ T * ρ) := by sorry

end QNatProofs
