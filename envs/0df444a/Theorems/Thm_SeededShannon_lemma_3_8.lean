-- Prove2me | Theorems.Thm_SeededShannon_lemma_3_8
-- name    : SeededShannon.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T05:22:53.365644+00:00
-- url     : https://prove2.me/theorems/5230bb5f-14ab-4205-8d9f-2c53f718198e
-- title:
--   Lemma 3.8 — soundness implies bounded decoding overlap
-- statement:
--   Let $\Pi_{\mathrm{PRC}}$ be a zero-bit public-key PRC with codeword length $\ell_{\mathrm{prc}}$, $\rho$-sound, and let $q=q(\lambda)\le\mathrm{poly}(\lambda)$ with $q(\lambda)\rho(\lambda)\le\tfrac12$ for every $\lambda$. Write $\mathrm{Fail}(\ell_0,\lambda)$ for the probability that, over $q$ independent key pairs, some word $w\in\{0,1\}^{\ell_{\mathrm{prc}}}$ is accepted by more than $\ell_0$ of the keys. Then:
--
--   1. for every $\lambda$ and every integer
--   $$\ell_0\ \ge\ \frac{\ell_{\mathrm{prc}}+\lambda}{\log_2(1/(q\rho))},$$
--   $\mathrm{Fail}(\ell_0,\lambda)\le 2^{-\lambda}$;
--   2. in particular $\mathrm{Fail}(\ell_{\mathrm{prc}}+\lambda,\lambda)\le 2^{-\lambda}$ for every $\lambda$;
--   3. if $\rho\le 2^{-c\,\ell_{\mathrm{prc}}}$ and $\ell_{\mathrm{prc}}\ge c'\lambda$ for constants $c,c'>0$ and all large $\lambda$, then one constant $\ell_0$ gives $\mathrm{Fail}(\ell_0,\lambda)\le 2^{-\lambda}$ for every $\lambda$.
--
--   Lemma 3.8 bounds the symbol lists of the puncturable pseudorandom code (Construction 4.2), independently of the number of keys.
--
--   **Formalization Note** When $q\rho=0$ the paper's threshold is $0$ ($\log_2\infty$); in Lean $1/0=0$ and $\log_2 0=0$ give the same threshold $0$.
--
--   Differences from the source:
--   - generalization: a zero-bit public-key pseudorandom code (Definition 3.5: efficient, pseudorandom) → any ZeroBitPRC syntax, with no efficiency or pseudorandomness assumed; reason: the lemma uses only ρ-soundness and independence of the keys; it specializes to every PRC of Definition 3.5
--   - encoding: ρ = 2^−Ω(ℓprc) and ℓprc = Ω(λ) → ρ ≤ 2^(−c·ℓprc) and c′·λ ≤ ℓprc from some λ₁ on, for constants c, c′ > 0; reason: the standard meaning of Ω
--   - reading: a constant ℓ0 suffices for the same failure bound → one ℓ0 with failure probability ≤ 2^−λ at every λ; reason: the literal reading of 'the same failure bound'
--   - encoding: threshold (ℓprc + λ)/log2(1/(qρ)) with qρ = 0 giving 0 → Lean's 1/0 = 0 and logb 2 0 = 0 give threshold 0; reason: same threshold
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), Lemma 3.8, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_SeededShannon_overlapFail

set_option autoImplicit false

namespace SeededShannon

open NoisyOWMPC

/-- **Lemma 3.8 (Soundness implies bounded overlap)** (Dujmovic, Lu, Silbak, Wichs, STOC 2027
submission (manuscript sha256 52f4b606…a769709), Lemma 3.8, p.19): let `Π_PRC` be a zero-bit
public-key PRC with codeword length `ℓprc`, `ρ`-sound, and let `q = q(λ) ≤ poly(λ)` with `qρ ≤ 1/2`.
Then
1. for every integer `ℓ0 ≥ (ℓprc + λ) / log₂(1/(qρ))`, the probability that some word is accepted
   by more than `ℓ0` of `q` independent keys is at most `2^{−λ}`;
2. in particular `ℓ0 = ℓprc + λ` suffices;
3. if `ρ = 2^{−Ω(ℓprc)}` and `ℓprc = Ω(λ)`, a constant `ℓ0` suffices for the same failure bound.

**Formalization Note** `Π_PRC` is only its syntax (`ZeroBitPRC`); no efficiency is used. The `Ω`'s
are explicit constants `c, c′ > 0` holding from some `λ₁` on. Lean's `1/0 = 0` and `log₂ 0 = 0`
make the threshold `0` when `qρ = 0`, where the failure probability is `0`. -/
theorem lemma_3_8 (P : ZeroBitPRC) (q : ℕ → ℕ) (ρ : ℕ → ℝ) (hq : PolyBounded q)
    (hsound : P.IsSound ρ) (hqρ : ∀ lam, (q lam : ℝ) * ρ lam ≤ 1 / 2) :
    (∀ lam ℓ0 : ℕ, ((P.n lam : ℝ) + lam) / Real.logb 2 (1 / ((q lam : ℝ) * ρ lam)) ≤ ℓ0 →
        overlapFail P q ℓ0 lam ≤ (2 : ℝ) ^ (-(lam : ℝ))) ∧
    (∀ lam : ℕ, overlapFail P q (P.n lam + lam) lam ≤ (2 : ℝ) ^ (-(lam : ℝ))) ∧
    ((∃ c : ℝ, 0 < c ∧ ∃ lam₁ : ℕ, ∀ lam ≥ lam₁, ρ lam ≤ (2 : ℝ) ^ (-(c * P.n lam))) →
      (∃ c' : ℝ, 0 < c' ∧ ∃ lam₁ : ℕ, ∀ lam ≥ lam₁, c' * lam ≤ P.n lam) →
      ∃ ℓ0 : ℕ, ∀ lam : ℕ, overlapFail P q ℓ0 lam ≤ (2 : ℝ) ^ (-(lam : ℝ))) := by sorry

end SeededShannon
