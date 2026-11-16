-- Prove2me | Theorems.Thm_PolynomialSampling137_OneThird_Supplement_theorem_22
-- name    : PolynomialSampling137.OneThird.Supplement.theorem_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:54:59.408555+00:00
-- url     : https://prove2.me/theorems/013656d0-0eff-4906-9063-3afb1f051021
-- title:
--   Theorem 22 — Uniform explicit inverse-line family with entropy floor(N/2^16), separating all (36) samplers up to (1+2^(−19))N nonlinear terms
-- statement:
--   Use the single deterministic padded inverse-line family $D_N$ of Eq. (49), with $h=2^{16}$ and $k=\lfloor N/h\rfloor$. Each $D_N$ is flat on $2^k$ points. One fixed deterministic bit program samples it from exactly $k$ fair bits in time $C(N+1)^a$ for all sufficiently large $N$. Define
--   $$\gamma=\frac12\min\left\{\frac12-\frac5{32}\log_2 9,\frac9{512}-\frac7{64h}\right\}>0.$$
--   There is one threshold $N_0$ such that for every $N\ge N_0$, every finite $s$, and every map $F$ of Eq. (36) with $M\le(1+2^{-19})N$,
--   $$\operatorname{Ov}(P_F,D_N)\le2^{-\gamma k}.$$
--   The entropy is $\Theta(N)$: eventually $N/(2h)\le k\le N/h$. There are absolute $a>0$ and a threshold for which the statistical distance from every such sampler is at least $1-2^{-aN}$. All thresholds and constants precede all source data. No small-bias claim is imposed on the zero padding. This companion theorem covers arbitrary affine parts, shared labels, dependent parity tests and outside-support outputs.
--
--   Differences from the source:
--   - encoding: finite binary vector spaces and probability laws → Fin-indexed words, finite fiber sums and structural predicates; reason: the representations preserve all source instances, including zero dimensions and zero masses
--   - encoding: fixed deterministic choices in Shoup construction and Gaussian elimination → the published specified Shoup constructor and ordered first-pivot elimination; reason: these fix permissible deterministic choices without changing the theorem; the runtime remains a conclusion in standard bit-machine semantics
--   - generalization: M counts the simplified nonlinear flat terms → M may also count redundant, empty, whole-space or codimension-one flat terms; reason: normalization only decreases M and preserves F, so every representation satisfies the source budget after simplification
--   - generalization: the target family is indexed by N at least one → the flatness conjunct also includes N zero; reason: the prescribed small-length point-mass definition extends to the empty word with k zero; all eventual separation and runtime claims keep their source domains
--   - generalization: there is an absolute constant γ > 0 → γ is the explicit value (1/2)min{1/2 − (5/32)log₂9, 9/512 − 7/(64h)} supplied by the proof (PDF p. 38); reason: the proof proves the bound with this γ, so the Lean statement implies the source's existential
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, Theorem 22, printed p. 25; PDF p. 27

import Definitions.Def_PolynomialSampling137_OneThird_Supplement_InverseConstructor

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

theorem theorem_22 :
    0 < InverseGamma ∧
    (∀ N : ℕ, Flat (N / InverseH) (InverseLaw N)) ∧
    (∃ (P : BitProgram) (C a N₀ : ℕ), 0 < C ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ x : Word (N / InverseH),
        P.ComputesWithin (C * (N+1)^a) (SamplerInput N x)
          (WordBits (InverseSampler N x))) ∧
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ (s M : ℕ),
      (M : ℝ) ≤ (1 + (2 : ℝ)^(-19 : ℤ)) * N →
      ∀ (A : Word s →ᵃ[ZMod 2] Word N) (v : Fin M → Word N)
        (B : Fin M → AffineSubspace (ZMod 2) (Word s)),
        overlap (samplerMass (FlatMap M A v B)) (InverseLaw N) ≤
          (2 : ℝ)^(-InverseGamma * (N / InverseH : ℕ))) ∧
    (∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ)/(2*InverseH) ≤ (N / InverseH : ℕ) ∧
      (N / InverseH : ℕ) ≤ (N : ℝ)/InverseH) ∧
    (∃ (a : ℝ) (N₀ : ℕ), 0 < a ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ (s M : ℕ), (M : ℝ) ≤ (1 + (2 : ℝ)^(-19 : ℤ)) * N →
      ∀ (A : Word s →ᵃ[ZMod 2] Word N) (v : Fin M → Word N)
        (B : Fin M → AffineSubspace (ZMod 2) (Word s)),
        1 - (2 : ℝ)^(-a * N) ≤
          (1/2 : ℝ) * ∑ y, |samplerMass (FlatMap M A v B) y - InverseLaw N y|) := by sorry

end PolynomialSampling137.OneThird.Supplement
