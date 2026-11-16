-- Prove2me | Theorems.Thm_SeededShannon_Supplement_theorem_3_6
-- name    : SeededShannon.Supplement.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:43:41.860206+00:00
-- url     : https://prove2.me/theorems/3988e102-7fd0-4dba-afb4-36b1c80b2b2b
-- title:
--   Theorem 3.6 — strong zero-bit PRCs from noisy McEliece
-- statement:
--   Let $\{C_\kappa\subseteq\mathbb F_2^m\}$ be an efficiently samplable family of binary linear codes of dimension $k$, with a deterministic polynomial-time list decoder at a fixed radius $a\in(0,1/2)$. Let $m\ge k\ge 2w$ be polynomially bounded parameters, where $w$ is the seed dimension of the Noisy McEliece assumption. Fix a target robustness $p\in[0,a)$, a public-key noise rate $\mu=\mu(\lambda)\in(0,1/2)$ and a constant ciphertext noise rate $\eta\in(0,1/2)$ satisfying
--   $$\mu=O(w^{-1/2}),\qquad \mu\cdot m=\omega(\log\lambda),\qquad p+\eta+2\mu^2 w\le a.$$
--   Under the binary Noisy McEliece assumption (Assumption B.1) for this family and these parameters, there is a zero-bit public-key pseudorandom code (Definition 3.5) of codeword length $m$ that is strongly $p$-robust and has soundness error $2^{-\Omega(m)}$.
--
--   This gives candidate strongly robust PRCs with robustness approaching $1/2$, the PRC assumption of Theorem 6.13.
--
--   **Formalization Note** As in Appendix B, all parameters are efficiently computable and polynomially bounded, and $\mu$ has a finite binary representation $\mu_{\mathrm{num}}/2^{\mu_{\mathrm{exp}}}$. The PRC is efficient and pseudorandom, as Definition 3.5 requires.
--
--   Differences from the source:
--   - reading: a strongly p-robust zero-bit public-key PRC → a published ZeroBitPRC with IsEfficient, Pseudorandom and StronglyRobust p, codeword length n = m; reason: a pseudorandom code of Definition 3.5 is efficient and pseudorandom; Appendix B proves both
--   - encoding: efficiently samplable family of binary linear codes of dimension k → a polynomial-time sampler and generator map with every sampled generator of rank k; reason: standard meaning of the phrase
--   - encoding: all parameters efficiently computable and polynomially bounded; public-key noise rates with finite binary representations (Appendix B, p.62) → PolyParam m, k, w, μexp; μ = μnum/2^μexp with μnum computable in polynomial time; reason: the standing conventions of Appendix B, stated as hypotheses
--   - encoding: μ = O(w^{−1/2}) → ∃ C λ₀, ∀ λ ≥ λ₀, μ(λ)·√w(λ) ≤ C; reason: the constant of O(·) quantified; the product form is defined at w = 0
--   - encoding: μ · m = ω(log λ) → ∀ C, ∃ λ₀, ∀ λ ≥ λ₀, C·log λ ≤ μ(λ)·m(λ); reason: definition of ω(·)
--   - encoding: soundness error 2^{−Ω(m)} → ∃ c > 0, λ₀: ρ-sound with ρ(λ) = 2^{−c·m(λ)} for λ ≥ λ₀ (ρ = 1 below); reason: the constant of Ω(·) quantified
--   - encoding: relative distance δ(v, G_κu) ≤ a; vectors over 𝔽₂ → Δ ≤ a·m; ZMod 2 vectors, bits via 1 ↦ true; reason: same instances for m ≥ 1
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 3.6, p.18 (PDF p.21); Assumption B.1, p.62 (PDF p.65); Construction B.2, p.63

import Mathlib
import Definitions.Def_KarpLiptonOM_binW
import Definitions.Def_SeededShannon_ZeroBitPRC
import Definitions.Def_SeededShannon_Supplement_NoisyMcEliece

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier NoisyOWMPC SeededShannon

/-- **Theorem 3.6 (Strong zero-bit PRCs from noisy McEliece [DJK+26])** (Dujmovic, Lu, Silbak, Wichs,
*Shannon Rate Seeded Codes from Indistinguishability Obfuscation*, STOC 2027 submission (manuscript
sha256 52f4b606…a769709), Theorem 3.6, p.18): let `{C_κ ⊆ 𝔽₂^m}` be an efficiently samplable family
of binary linear codes of dimension `k`, with a deterministic polynomial-time list decoder at a
fixed radius `a ∈ (0, 1/2)`. Let `m ≥ k ≥ 2w` be polynomially bounded parameters, `w` the seed
dimension of the assumption. Fix a target robustness `p ∈ [0, a)`, a public-key noise rate
`μ = μ(λ) ∈ (0, 1/2)` and a constant ciphertext noise rate `η ∈ (0, 1/2)` with
`μ = O(w^{−1/2})`, `μ · m = ω(log λ)` and `p + η + 2 · μ² · w ≤ a`. Under the binary Noisy McEliece
assumption for this family and these parameters (Assumption B.1), there is a strongly `p`-robust
zero-bit public-key PRC of codeword length `m` with soundness error `2^{−Ω(m)}`.

**Formalization Note** The PRC is the published `SeededShannon.ZeroBitPRC` (Definition 3.5),
efficient and pseudorandom. Appendix B's standing conventions (p.62) are hypotheses: all parameters
are efficiently computable and polynomially bounded (`PolyParam`), and `μ` has a finite binary
representation `μnum/2^{μexp}` (exact Bernoulli sampling), computable in polynomial time.
`μ = O(w^{−1/2})` is `μ(λ) · √w(λ) ≤ C` for `λ ≥ λ₀`; `μ · m = ω(log λ)` is
`∀ C, ∃ λ₀, ∀ λ ≥ λ₀, C · log λ ≤ μ(λ) · m(λ)`; soundness error `2^{−Ω(m)}` is `ρ`-soundness with
`ρ(λ) = 2^{−c · m(λ)}` for `λ ≥ λ₀` (and the trivial `ρ = 1` below), for some `c > 0`. Relative
distances `δ ≤ a` are `Δ ≤ a · m`. -/
theorem theorem_3_6 (F : LinCodeFamily) (w μnum μexp : ℕ → ℕ) (a p η : ℝ)
    (dec : (lam : ℕ) → List Bool → (Fin (F.m lam) → ZMod 2) → List (Fin (F.k lam) → ZMod 2))
    (hF : F.IsSamplable) (hdec : F.IsListDecoder a dec) (ha : 0 < a) (ha2 : a < 1 / 2)
    (hm : PolyParam F.m) (hk : PolyParam F.k) (hw : PolyParam w)
    (hmkw : ∀ lam, 2 * w lam ≤ F.k lam ∧ F.k lam ≤ F.m lam)
    (hp : 0 ≤ p) (hpa : p < a)
    (hμ : ∀ lam, 0 < dyadic μnum μexp lam ∧ dyadic μnum μexp lam < 1 / 2)
    (hμexp : PolyParam μexp)
    (hμnum : PolyTimeOn (ι := ℕ) (fun lam => [unary lam])
      (fun lam => KarpLiptonOM.binW (μexp lam) (μnum lam)))
    (hη : 0 < η ∧ η < 1 / 2)
    (hμw : ∃ (C : ℝ) (lam₀ : ℕ), ∀ lam ≥ lam₀, dyadic μnum μexp lam * Real.sqrt (w lam) ≤ C)
    (hμm : ∀ C : ℝ, ∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
      C * Real.log lam ≤ dyadic μnum μexp lam * F.m lam)
    (hsum : ∀ lam, p + η + 2 * dyadic μnum μexp lam ^ 2 * w lam ≤ a)
    (hNM : NoisyMcEliece F w μnum μexp η) :
    ∃ P : ZeroBitPRC, P.n = F.m ∧ P.IsEfficient ∧ P.Pseudorandom ∧ P.StronglyRobust p ∧
      ∃ c : ℝ, 0 < c ∧ ∃ lam₀ : ℕ,
        P.IsSound (fun lam => if lam₀ ≤ lam then (2 : ℝ) ^ (-(c * F.m lam)) else 1) := by sorry

end SeededShannon.Supplement
