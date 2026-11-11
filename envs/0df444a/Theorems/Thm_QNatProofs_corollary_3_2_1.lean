-- Prove2me | Theorems.Thm_QNatProofs_corollary_3_2_1
-- name    : QNatProofs.corollary_3_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:35.0802+00:00
-- url     : https://prove2.me/theorems/852ee8a8-9a85-4a04-8e70-d21a526c27fa
-- title:
--   Corollary 3.2.1 — parameters for random-function security
-- statement:
--   Let $N=2^n\ge2$, $T\in\mathbb N$, and $\varepsilon\in(0,1)$ with $\varepsilon\ge2e^{-N/8}$. Let $C\ge1$ be a constant for which Theorem 3.1 holds, and let $\mathrm{Samp}$ be an $(s,\xi,\eta_{\mathrm{samp}})$-complex Gaussian sampler with
--   $$
--   s\ge\tfrac12,\qquad \xi\le\frac{\varepsilon}{16CN^{3/2}2^T},\qquad \eta_{\mathrm{samp}}\le\frac{\varepsilon}{4N}.\tag{20}
--   $$
--   Then for $\gamma=1/(2s)$,
--   $$
--   \mathrm{TVD}\big(\mathrm{al}_T(D_{\mathrm{rf}}),\mathrm{al}_T(\mathrm{Haar}_n)\big)\le\varepsilon.\tag{21}
--   $$
--
--   This turns Theorem 3.1 into explicit sampler requirements, which Lemma 4.1's sampler meets (p.25).
--
--   Differences from the source:
--   - encoding: C ≥ 1 a universal constant for which Theorem 3.1 holds → hypotheses 1 ≤ C and Thm31Const C; reason: the bound of Theorem 3.1 with that C, as a predicate
--   - encoding: binary encoding of the polar coordinates (r, θ) ∈ [0,1)² (Definition 3.1) → two q-bit binary fractions, most significant bit first (Sampler R q); reason: any finite binary-fraction encoding becomes one of this form by padding with zeros, which changes no encoded complex number
--   - encoding: TVD of the laws of al_T → tvdAl, a finite sum over amplitude-list strings; reason: al_T takes finitely many values
--   - reading: al_T(ψ): polar coordinates written to T fractional bits → QNatProofs.al: basis strings in increasing binary order, r-bits then θ-bits, truncation ⌊2^T r⌋ capped at 2^T−1 (so r = 1 is written 1⋯1), θ = arg/(2π) mod 1 with θ(0) = 0; reason: the printed codomain {0,1}^{2T·2^n} forces the cap; the order and θ(0) are unspecified on p.8
--   - encoding: Haar_n, the Haar probability measure on the unit sphere of ℂ^{2^n} → the surface measure toSphere of an additive Haar measure on EuclideanSpace ℂ (Qubits n), normalized to mass 1; reason: the unique rotation-invariant probability measure on the sphere; same measure
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Corollary 3.2.1, (20)–(21), p.15; proof p.15

import Mathlib
import Definitions.Def_QNatProofs_psiState

set_option autoImplicit false

namespace QNatProofs

/-- **Corollary 3.2.1 (Parameters for random function security)** (Li, Parham, *Natural proofs for
quantum state preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.15): "Let
`N = 2ⁿ ≥ 2`, let `T ∈ ℕ`, and let `ε ∈ (0, 1)` satisfying `ε ≥ 2e^{-N/8}`. Let `C ≥ 1` be a
universal constant for which Theorem 3.1 holds, and let `Samp` be a complex Gaussian sampler as in
Definition 3.1 with parameters `s ≥ 1/2`, `ξ ≤ ε/(16 C N^{3/2} 2^T)`, `η_samp ≤ ε/(4N)`. (20)
Then for `γ = 1/(2s)`, the state ensemble `D_rf` defined using `Samp` and `γ` is `ε`-close to the
Haar measure when viewing only truncated amplitude lists at precision `T`:
`TVD(al_T(D_rf), al_T(Haar_n)) ≤ ε`. (21)" -/
theorem corollary_3_2_1 (C : ℝ) (hC : 1 ≤ C) (hC31 : Thm31Const C) (n : ℕ) (hn : 2 ≤ 2 ^ n)
    (T : ℕ) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hεN : 2 * Real.exp (-((2 : ℝ) ^ n / 8)) ≤ ε) {R q : ℕ} (Samp : Sampler R q) (s ξ η : ℝ)
    (hSamp : IsComplexGaussianSampler s ξ η Samp) (hs : 1 / 2 ≤ s)
    (hξ : ξ ≤ ε / (16 * C * ((2 : ℝ) ^ n) ^ ((3 : ℝ) / 2) * (2 : ℝ) ^ T))
    (hη : η ≤ ε / (4 * (2 : ℝ) ^ n)) :
    tvdAl T (Drf n (1 / (2 * s)) Samp) (haar n) ≤ ε := by sorry

end QNatProofs
