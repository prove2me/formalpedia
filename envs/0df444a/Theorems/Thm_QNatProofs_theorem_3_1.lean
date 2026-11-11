-- Prove2me | Theorems.Thm_QNatProofs_theorem_3_1
-- name    : QNatProofs.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:45.250855+00:00
-- url     : https://prove2.me/theorems/a8c6b44a-cba0-4753-9a24-58c5297e67ef
-- title:
--   Theorem 3.1 — random-function security
-- statement:
--   There is a universal constant $C>0$ with the following property. Fix $n\ge1$, $N=2^n$, and $\gamma\in(0,1]$. Let $\mathrm{Samp}$ be an $(s,\xi,\eta_{\mathrm{samp}})$-complex Gaussian sampler and $D_{\mathrm{rf}}$ the law of $|\psi_{H,\gamma}\rangle$ for a uniformly random $H$. If $\beta\in(0,1)$ satisfies $s\gamma+\xi\le\beta$, then for every truncation precision $T\in\mathbb N$,
--   $$
--   \mathrm{TVD}\big(\mathrm{al}_T(D_{\mathrm{rf}}),\mathrm{al}_T(\mathrm{Haar}_n)\big)\le N\eta_{\mathrm{samp}}+e^{-N(1-\beta^2)^2/2}+CN^{3/2}2^T\cdot\frac{2\xi}{\beta}.\tag{8}
--   $$
--
--   This is the statistical half of the PRAL construction: with a truly random function, the truncated amplitude lists are close to Haar.
--
--   Differences from the source:
--   - encoding: C > 0 a universal constant → ∃ C, 0 < C ∧ Thm31Const C, the bound for every n ≥ 1, γ, sampler, β and T; reason: C is chosen before all of them, as 'universal' says
--   - encoding: binary encoding of the polar coordinates (r, θ) ∈ [0,1)² (Definition 3.1) → two q-bit binary fractions, most significant bit first (Sampler R q); reason: any finite binary-fraction encoding becomes one of this form by padding with zeros, which changes no encoded complex number
--   - encoding: TVD of the laws of al_T → ½ Σ_s |μ{al_T = s} − ν{al_T = s}| over the strings of length T·2^{n+1} (tvdAl); reason: al_T takes finitely many values
--   - encoding: D_rf, the distribution of |ψ_H⟩ for uniform H → the uniform mixture of the point masses at ψ_{f_H,γ} over all H, including the |0ⁿ⟩ branch; reason: same law
--   - reading: al_T(ψ): polar coordinates written to T fractional bits → QNatProofs.al: basis strings in increasing binary order, r-bits then θ-bits, truncation ⌊2^T r⌋ capped at 2^T−1 (so r = 1 is written 1⋯1), θ = arg/(2π) mod 1 with θ(0) = 0; reason: the printed codomain {0,1}^{2T·2^n} forces the cap; the order and θ(0) are unspecified on p.8
--   - encoding: Haar_n, the Haar probability measure on the unit sphere of ℂ^{2^n} → the surface measure toSphere of an additive Haar measure on EuclideanSpace ℂ (Qubits n), normalized to mass 1; reason: the unique rotation-invariant probability measure on the sphere; same measure
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Theorem 3.1, (8), p.12; proof p.13–14

import Mathlib
import Definitions.Def_QNatProofs_psiState

set_option autoImplicit false

namespace QNatProofs

/-- **Theorem 3.1 (Random-function security)** (Li, Parham, *Natural proofs for quantum state
preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.12): "Fix `n ≥ 1`, write
`N = 2ⁿ`, and let `γ ∈ (0, 1]`. Let `Samp` be an `(s, ξ, η_samp)`-complex Gaussian sampler, and let
`D_rf` be the distribution over states `|ψ_H⟩` defined by this sampler and threshold for uniformly
random `H`. Suppose there exists `β ∈ (0, 1)` such that `sγ + ξ ≤ β`. Then, for every truncation
precision `T ∈ ℕ`,
`TVD(al_T(D_rf), al_T(Haar_n)) ≤ Nη_samp + e^{-N(1−β²)²/2} + C N^{3/2} 2^T · 2ξ/β`, (8)
where `C > 0` is a universal constant."

**Formalization Note** `Thm31Const C` is the displayed bound for every `n ≥ 1`, `γ`, sampler, `β`
and `T`; the constant `C > 0` is chosen before all of them. -/
theorem theorem_3_1 : ∃ C : ℝ, 0 < C ∧ Thm31Const C := by sorry

end QNatProofs
