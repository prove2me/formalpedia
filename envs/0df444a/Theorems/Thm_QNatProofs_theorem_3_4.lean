-- Prove2me | Theorems.Thm_QNatProofs_theorem_3_4
-- name    : QNatProofs.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:06:11.513688+00:00
-- url     : https://prove2.me/theorems/044147cf-63ea-41b3-8783-dc8fe481b0d6
-- title:
--   Theorem 3.4 — PRAL security from subexponentially secure PRFs
-- statement:
--   Let $\mathcal G$ be classically subexponentially secure with exponent $a\in(0,1)$ and let $C\ge1$ be a constant for which Theorem 3.1 holds. Suppose a sampler family gives, for every $n$, $T$ and requested tolerance $\varepsilon=2^{-j}$ ($j\ge1$), an $(s,\xi,\eta)$-complex Gaussian sampler satisfying the bounds of Corollary 3.2.1,
--   $$
--   s\ge\tfrac12,\qquad\xi\le\frac{\varepsilon}{16CN^{3/2}2^T},\qquad\eta\le\frac{\varepsilon}{4N},
--   $$
--   whose tape length is polynomial in $n+T+j$, which one classical machine evaluates in time polynomial in $n+T+j$, and whose $s^2=1/(4\gamma^2)$ is rational and computable in that time. Then the target-state distributions $D_{n,\lambda,T}$ of the proof (with $\varepsilon=2^{-\lambda-1}$, $\gamma=1/(2s)$, PRF security parameter $\kappa=n^2+\lambda+1$ and the family of Fact 3.2) form a PRAL family.
--
--   Together with Corollary 4.6.2 this gives the PRAL family of the main theorem.
--
--   Differences from the source:
--   - generalization: Definition 3.2: there is a ∈ (0,1) such that for all sufficiently large m every oracle algorithm B of time ≤ 2^{m^a} has advantage ≤ 2^{−m^a} → ∃ a ∈ (0,1), ∀ uniform oracle algorithm B, ∀ᶠ m, for every auxiliary input z with |z| ≤ m: time ≤ 2^{m^a} on 1^m z → advantage ≤ 2^{−m^a} (IsSecureWithExp); reason: the threshold may depend on B, so the hypothesis is implied by the printed one (where for each large m every algorithm, which may hard-wire z, is covered)
--   - generalization: 𝒢 has uniform keys sampled in poly(m) time and functions evaluated in poly(m) time → KeyedFam: any nonempty finite key sets with the uniform law; no efficiency clauses; reason: weaker hypothesis; no step of the proof samples keys or evaluates 𝒢 classically (the reductions only query the oracle; PRAL needs no efficient sampling, p.9)
--   - generalization: for every requested error tolerance ε ∈ (0, 1) there is a sampler → a sampler only for ε = 2^{−j}, j ≥ 1; reason: a weaker hypothesis; the proof uses ε = 2^{−λ−1}
--   - reading: tape length and classical evaluation time polynomial in n, T and log(1/ε) → one polynomial bounds R by p(n + T + j); one FinTM2 machine evaluates every sampler from the unary codes of (n, T, j) and the tape within p(n + T + j) steps; s² is rational and computed by one machine in that time; reason: p.25 lists γ² = 1/(4µ) rational and efficiently computable among 'the sampler and classical-computation requirements used in Theorem 3.4'; the proof's appeal to Theorem 3.3 needs it
--   - generalization: the sampler and PRF parameters can be chosen so that the target-state distributions form a PRAL family → IsPRAL of the explicit choice pralFamily (ε = 2^{−λ−1}, γ = 1/(2s), κ = n² + λ + 1, Fact 3.2's family); reason: the explicit choice of the proof implies the existential statement
--   - encoding: probability over ψ ← D and the coins of A; A probabilistic polynomial time → Σ_s D{al_T = s}·Pr_coins[A(1^n,1^λ,s) = 1] over the strings s of length T·2^{n+1}; A a CoinAlg with polynomially many coins and one polynomial-time FinTM2 machine (IsPPT), input 1^n0 1^λ0 s; reason: al_T takes finitely many values; a finite sum avoids integrals of possibly non-measurable functions
--   - reading: al_T(ψ): polar coordinates written to T fractional bits → QNatProofs.al: basis strings in increasing binary order, r-bits then θ-bits, truncation ⌊2^T r⌋ capped at 2^T−1 (so r = 1 is written 1⋯1), θ = arg/(2π) mod 1 with θ(0) = 0; reason: the printed codomain {0,1}^{2T·2^n} forces the cap; the order and θ(0) are unspecified on p.8
--   - encoding: binary encoding of the polar coordinates (r, θ) ∈ [0,1)² (Definition 3.1) → two q-bit binary fractions, most significant bit first (Sampler R q); reason: any finite binary-fraction encoding becomes one of this form by padding with zeros, which changes no encoded complex number
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Theorem 3.4, p.17; proof p.17; 'Compatibility with security parameters', p.25

import Mathlib
import Definitions.Def_QNatProofs_pralFamily

set_option autoImplicit false

namespace QNatProofs

open Polynomial

/-- **Theorem 3.4 (PRAL security from subexponentially secure PRFs)** (Li, Parham, *Natural proofs
for quantum state preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.17):
"Let `𝒢` be a classically subexponentially secure PRF family in the sense of Definition 3.2.
Suppose that for every requested error tolerance `ε ∈ (0, 1)`, there is a complex Gaussian sampler
satisfying the parameter bounds of Corollary 3.2.1, with tape length and classical evaluation time
polynomial in `n`, `T`, and `log(1/ε)`. Then the sampler and PRF parameters can be chosen so that
the resulting target-state distributions `{D_{n,λ,T}}` form a PRAL family."

The parameters are those of the proof (p.17): `ε = 2^{-λ-1}`, `γ = 1/(2s)`, PRF security parameter
`κ = n² + λ + 1` with the family of Fact 3.2 (`pralFamily`).

**Formalization Note** The sampler family is indexed by `(n, T, j)` for the requested tolerance
`ε = 2^{-j}`, `j ≥ 1`. "Classical evaluation time polynomial" is one machine and one polynomial for
the whole family; it includes computing the rational number `s² = 1/(4γ²)`, which the proof's
appeal to Theorem 3.3 needs ("`γ²` is rational and computable"). `C ≥ 1` is a constant for which
Theorem 3.1 holds. -/
theorem theorem_3_4 (G : KeyedFam) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (hG : G.IsSecureWithExp a) (C : ℝ) (hC : 1 ≤ C) (hC31 : Thm31Const C) (SF : SamplerFamily)
    (hsamp : ∀ n T j : ℕ, 1 ≤ j → ∃ ξ η : ℝ,
      IsComplexGaussianSampler (SF.s n T j) ξ η (SF.samp n T j) ∧ 1 / 2 ≤ SF.s n T j ∧
      ξ ≤ (2 : ℝ)⁻¹ ^ j / (16 * C * ((2 : ℝ) ^ n) ^ ((3 : ℝ) / 2) * (2 : ℝ) ^ T) ∧
      η ≤ (2 : ℝ)⁻¹ ^ j / (4 * (2 : ℝ) ^ n))
    (hlen : ∃ p : ℕ[X], ∀ n T j : ℕ, 1 ≤ j → SF.R n T j ≤ p.eval (n + T + j))
    (heval : ∃ (M : Turing.TM2ComputableAux Bool Bool) (p : ℕ[X]), ∀ n T j : ℕ, 1 ≤ j →
      ∀ ω : Fin (SF.R n T j) → Bool,
        MachineComputesIn M
          (QAlgorithms.Complexity.encNat n ++ QAlgorithms.Complexity.encNat T ++
            QAlgorithms.Complexity.encNat j ++ List.ofFn ω)
          (List.ofFn (SF.samp n T j ω).1 ++ List.ofFn (SF.samp n T j ω).2) (p.eval (n + T + j)))
    (hgam : ∃ (M : Turing.TM2ComputableAux Bool Bool) (p : ℕ[X]), ∀ n T j : ℕ, 1 ≤ j →
      ∃ r : ℚ, SF.s n T j ^ 2 = r ∧
        MachineComputesIn M
          (QAlgorithms.Complexity.encNat n ++ QAlgorithms.Complexity.encNat T ++
            QAlgorithms.Complexity.encNat j)
          (PPADSIS.SubexpSIS.encInt r.num ++ PPADSIS.SubexpSIS.encNat r.den)
          (p.eval (n + T + j))) :
    IsPRAL (pralFamily G a SF) := by sorry

end QNatProofs
