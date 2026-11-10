-- Prove2me | Theorems.Thm_SeededShannon_theorem_5_6
-- name    : SeededShannon.theorem_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T05:23:00.105291+00:00
-- url     : https://prove2.me/theorems/f0a7d4d5-f63c-4914-b1f6-5f1745620e16
-- title:
--   Theorem 5.6 — sparse partition agreement embedding
-- statement:
--   Fix constants $0<p<\tau<1/2$ and $0<\gamma<p/\tau$. For every sufficiently large fixed integer $b$ there are a polynomial $N_{\min}$ and a recoverable embedding (Definition 5.4) with minimum input length $N_{\min}$ for the family indexed by partitions $P$ of $[n]$ into blocks of size $b$ ($n\ge N_{\min}(\lambda)$, $b\mid n$), where $f_P$ is described by $P$ and
--   $$f_P(y)=1\iff \mathrm{wt}(y)\le p\cdot n\ \text{ and }\ |\{S\in P:\mathrm{wt}(y_S)>\tau\cdot b\}|>\gamma\cdot n/b.$$
--   The sampled parameters are perfectly recoverable with probability $1-\mathrm{negl}(\lambda)$, simultaneously for all inputs and all seeds; recovery is deterministic and has a polynomial output-list bound.
--
--   With Theorem A.1 it gives the partition obfuscator of Theorem 5.3.
--
--   **Formalization Note** Partitions are block labellings; "described by $P$" is a polynomial-time map from the sampled description to the code of $P$, with the description evaluating to $f_P$. The recoverability clause is the correctness clause of Definition 5.4.
--
--   Differences from the source:
--   - encoding: every sufficiently large fixed integer b → ∃ b₀, ∀ b ≥ b₀; reason: standard meaning
--   - encoding: f_P is described by P → a polynomial-time map from the sampled description to the code of a partition P, and the description evaluates to f_P; reason: a description determines P efficiently and computes f_P
--   - encoding: perfectly recoverable with probability 1 − negl(λ) for every polynomially bounded n → the correctness clause of Definition 5.4 (for every bound n ≤ (λ+2)^c a negligible ν); reason: the paper's 'for every polynomially bounded n ≥ N_min(λ)'
--   - encoding: for every polynomially bounded n (every polynomial P) → pointwise clauses for all n ≥ N_min(λ); probabilistic clauses for every bound n ≤ (λ+2)^c; reason: the pointwise clauses hold at each length, and every polynomial is bounded by some (λ+2)^c
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Theorem 5.6, p.33 (PDF p.36)

import Mathlib
import Definitions.Def_SeededShannon_RecEmb
import Definitions.Def_SeededShannon_balP
import Definitions.Def_SeededShannon_SeededCode

set_option autoImplicit false

namespace SeededShannon

open LaconicBarrier NoisyOWMPC

/-- **Theorem 5.6 (Sparse Partition Agreement Embedding)** (Dujmovic, Lu, Silbak, Wichs, STOC 2027
submission (manuscript sha256 52f4b606…a769709), Theorem 5.6, p.33): fix constants
`0 < p < τ < 1/2` and `0 < γ < p/τ`. For every sufficiently large fixed integer `b` there are a
polynomial `N_min` and a recoverable embedding with minimum input length `N_min` for the family
indexed by partitions `P` of `[n]` into blocks of size `b` (`n ≥ N_min(λ)` divisible by `b`), where
`f_P` is described by `P` and `f_P(y) = 1 ⟺ wt(y) ≤ p · n` and
`|{S ∈ P : wt(y_S) > τ · b}| > γ · n/b`. The sampled parameters are perfectly recoverable with
probability `1 − negl(λ)`, simultaneously for all inputs and all seeds; recovery is deterministic
and has a polynomial output-list bound.

**Formalization Note** "Sufficiently large fixed integer `b`" is `∃ b₀, ∀ b ≥ b₀`. Partitions are
block labellings (`IsBlockPartition`); "`f_P` is described by `P`" is: a polynomial-time map
`partOf` reads the code of `P` off the sampled description, and the description evaluates to `f_P`.
The recoverability clause is the correctness clause of `RecEmb.IsRecEmb` (Definition 5.4). -/
theorem theorem_5_6 (p τ γ : ℝ) (hp : 0 < p) (hpτ : p < τ) (hτ : τ < 1 / 2) (hγ : 0 < γ)
    (hγτ : γ < p / τ) :
    ∃ b₀ : ℕ, ∀ b ≥ b₀, ∃ (Nmin : ℕ → ℕ) (E : RecEmb) (partOf : ℕ → ℕ → List Bool → List Bool)
      (L : ℕ → ℕ → ℕ),
      E.IsRecEmb Nmin (fun _ n => b ∣ n) (partFamily56 p τ γ b) ∧
      PolyTimeOn (ι := (z : {z : ℕ × ℕ // Nmin z.1 ≤ z.2 ∧ b ∣ z.2}) ×
          (Fin (E.ppCoins z.1.1 z.1.2) → Bool) × (Fin z.1.1 → Bool))
        (fun i => [unary i.1.1.1, unary i.1.1.2,
          E.sampleFunc (E.sampleParams i.1.1.1 i.1.1.2 i.2.1) (bits i.2.2)])
        (fun i => partOf i.1.1.1 i.1.1.2
          (E.sampleFunc (E.sampleParams i.1.1.1 i.1.1.2 i.2.1) (bits i.2.2))) ∧
      (∀ lam n, Nmin lam ≤ n → b ∣ n →
        ∀ (r : Fin (E.ppCoins lam n) → Bool) (u : Fin lam → Bool),
          ∃ P : Fin n → ℕ, IsBlockPartition b n P ∧
            partOf lam n (E.sampleFunc (E.sampleParams lam n r) (bits u)) = partCode P ∧
            ∀ y : Fin n → Bool,
              E.evalDesc (E.sampleFunc (E.sampleParams lam n r) (bits u)) (bits y) = true ↔
                partAgree p τ γ b P y) ∧
      PolyBounded₂ L ∧
      ∀ lam n, Nmin lam ≤ n → b ∣ n → ∀ (r : Fin (E.ppCoins lam n) → Bool) (y : Fin n → Bool),
        (E.recoverSeeds (E.sampleParams lam n r) (bits y)).length ≤ L lam n := by sorry

end SeededShannon
