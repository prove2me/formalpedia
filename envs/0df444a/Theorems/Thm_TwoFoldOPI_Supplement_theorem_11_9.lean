-- Prove2me | Theorems.Thm_TwoFoldOPI_Supplement_theorem_11_9
-- name    : TwoFoldOPI.Supplement.theorem_11_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:12:30.821996+00:00
-- url     : https://prove2.me/theorems/0b9c3fc0-3aba-413e-965e-ac1d840f4da0
-- title:
--   Theorem 11.9 — proof of quantumness
-- statement:
--   Let $B_1,\dots,B_R$ and $\alpha_1,\dots,\alpha_R$ be admissible with $\eta=1$, let $p_{\mathrm{stay}}=\Pr[K_{\mathrm{src}}-1\in B_{I_{\mathrm{src}}}]\Pr[K_{\mathrm{tar}}+1\in B_{I_{\mathrm{tar}}}]$, and let $\tau=\sum_r\alpha_r\tau_r$ be the weighted tail threshold. Suppose $1-p_{\mathrm{stay}}<\min\{\tau,1\}$ and choose the rate of $C_\lambda$ with
--   $$1-p_{\mathrm{stay}}<\rho<\min\{\tau,1\}.$$
--   Then the protocol $\Pi_{\mathrm{base}}$ — the quantum prover runs the algorithm of Theorem 11.3 and sends its output $x$; the classical verifier checks $x\in C_\lambda$, queries $H_i(x_i)$ for every block and accepts iff $(H_1(x_1),\dots,H_m(x_m))\in\mathcal T$ — is a keyless noninteractive publicly verifiable proof of quantumness: the honest quantum prover is accepted with probability $\Omega(1)$, and every computationally unbounded classical prover making polynomially many classical queries is accepted with probability $2^{-\Omega(\lambda)}$.
--
--   This adapts the Yamakawa–Zhandry random-oracle separation to load constraints.
--
--   Differences from the source:
--   - generalization: an explicitly represented F_q and an arbitrary generator γ → both claims hold for every explicit presentation of F_q and every generator γ; reason: specializes to any fixed choice
--   - reading: the honest prover runs the algorithm of Theorem 11.3 → there is a uniform quantum algorithm with the guarantees of Theorem 11.3 that serves as the honest prover; reason: Theorem 11.3 is existential, so Π_base is determined by such an algorithm
--   - encoding: every computationally unbounded classical prover making polynomially many classical queries → every deterministic query tree with at most Q(λ) queries on every oracle, for every polynomial Q; reason: randomized provers are mixtures of deterministic trees, so the bound covers them
--   - encoding: Ω(1) and 2^{−Ω(λ)} → a constant c > 0 for all λ ≥ λ₀; for every Q, a constant c′ > 0 and λ₁ with acceptance at most 2^{−c′λ} for λ ≥ λ₁; reason: explicit quantifiers; c′ may depend on the query polynomial
--   - encoding: Suppose 1 − p_stay < min{τ, 1}; τ ∈ [0, ∞] → not repeated; ρ < τ is stated in [0, ∞] as ofReal ρ < τ; reason: the hypothesis is implied by the choice of ρ
--   - encoding: on failure the prover sends a fixed dummy string → a failure leaf counts as rejection; reason: this can only lower the acceptance probability, so completeness is not weakened
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11.3, Theorem 11.9, p. 62

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
import Definitions.Def_QAlgorithms_Defs_OPIUniformity
import Definitions.Def_TwoFoldOPI_elemBits
import Definitions.Def_TwoFoldOPI_decodeWord
import Definitions.Def_TwoFoldOPI_Supplement_readBits
import Definitions.Def_TwoFoldOPI_Supplement_Admissible
import Definitions.Def_TwoFoldOPI_Supplement_pStay
import Definitions.Def_TwoFoldOPI_Supplement_tailThreshold
import Definitions.Def_TwoFoldOPI_Supplement_canonicalPartition
import Definitions.Def_TwoFoldOPI_Supplement_DLamInput
import Definitions.Def_TwoFoldOPI_Supplement_blockOracle
import Definitions.Def_TwoFoldOPI_Supplement_blockSuccess
import Definitions.Def_TwoFoldOPI_Supplement_QTree

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms QAlgorithms.OPI

open Classical in
/-- **Theorem 11.9 (proof of quantumness).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11.3, Theorem 11.9, p.62: "Assume that B_1, …, B_R and α_1, …, α_R are admissible
(Definition 10.9) with η = 1. Let p_stay = Pr[K_src − 1 ∈ B_{I_src}] Pr[K_tar + 1 ∈ B_{I_tar}], using
the distributions from Theorem 10.11, and let τ = Σ_r α_r τ_r be the weighted tail threshold
(Definition 11.5). Suppose 1 − p_stay < min{τ, 1}. Choose the rate parameter ρ of C_λ
(Definition 11.1) to satisfy 1 − p_stay < ρ < min{τ, 1}. Then Π_base (Definition 11.7) is a keyless
noninteractive publicly verifiable proof of quantumness with constant completeness and negligible
classical soundness: the honest quantum prover is accepted with probability Ω(1), whereas every
computationally unbounded classical prover making polynomially many classical queries is accepted
with probability 2^{−Ω(λ)}."; Definition 11.7, p.61: "In the keyless noninteractive protocol Π_base,
the quantum prover runs the algorithm of Theorem 11.3 and sends its output x ∈ (F_q^s)^m. On
failure, it sends a fixed dummy string. The classical verifier checks that the unfolded vector x
belongs to C_λ, queries H_i(x_i) for every i ∈ [m], and accepts exactly when
(H_1(x_1), …, H_m(x_m)) ∈ T."

With the parameters of Definition 11.1 (`ℓ = ⌊log₂ λ⌋`, `q = 2^{2ℓ}`, `M = q − 1`, `s = 2^ℓ + 1`,
`n = 2^ℓ`, `m = M/s`, `k = ⌊ρM⌋`), the verifier of `Π_base` accepts `x` exactly when
`x ∈ C_λ ∩ A_{H_1,…,H_m}` (`blockSuccess`). There is an honest prover, a uniform quantum algorithm
`A` (the algorithm of Theorem 11.3), such that:
1. (completeness) there are `P`, `c > 0` and `λ₀` such that for all `λ ≥ λ₀`, all presentations `F`
   of `F_q` and generators `γ`: `A` uses at most `P(λ)` charged resources on every oracle, and its
   message is accepted with probability `≥ c` over uniform `H_1, …, H_m` and its internal
   randomness;
2. (soundness) for every polynomial `Q` there are `c' > 0` and `λ₁` such that for all `λ ≥ λ₁`,
   `F`, `γ` and every classical prover `T` (a query tree) making at most `Q(λ)` queries to the
   `H_i` on every oracle, its message is accepted with probability `≤ 2^{−c'λ}` over uniform
   `H_1, …, H_m`.

**Formalization Note.** `Ω(1)` and `2^{−Ω(λ)}` are a constant `c > 0` and `2^{−c'λ}`; `c'` may depend on
the query polynomial `Q` and nothing else about the prover. A classical prover is a deterministic
query tree (`QTree`) with unrestricted local computation; a randomized one is a mixture of these,
so the bound covers it. Keyless, noninteractive and publicly verifiable hold by the form of
`Π_base` (one message, no setup, a classical verifier using only public data and `m` oracle
queries). The hypothesis `1 − p_stay < min{τ, 1}` is implied by the choice of `ρ` and is not
repeated; `τ` is `weightedTail` in `[0, ∞]` and `ρ < τ` is `ofReal ρ < τ`. Completeness counts only
real outputs (a failure leaf counts as rejection), which can only lower the acceptance
probability of the dummy-string convention. -/
theorem theorem_11_9 {R : ℕ} [NeZero R] (B : Fin R → Set ℕ) (α : Fin R → ℝ) (ν : ℝ)
    (hadm : Admissible B α 1 ν) (ρ : ℝ) (hρ0 : 0 < ρ) (hgap : 1 - pStay B α 1 ν < ρ)
    (hρ1 : ρ < 1) (hτ : ENNReal.ofReal ρ < weightedTail B α) :
    ∃ A : UniformResourceFamily (DLamInput R) DLamInput.encode DLamInput.scale,
      (∀ x : DLamInput R,
        (A.construct x).oracles = (2 ^ (2 * Nat.log 2 x.lam) - 1) / (2 ^ Nat.log 2 x.lam + 1) ∧
        (∀ k, (A.construct x).arity k = (2 ^ Nat.log 2 x.lam + 1) * bitsPerSymbol x.F +
          Nat.clog 2 (2 ^ Nat.log 2 x.lam)) ∧
        (A.construct x).outputBits = (Fintype.card x.F.F - 1) * bitsPerSymbol x.F) ∧
      (∃ (P : Polynomial ℕ) (c : ℝ), 0 < c ∧ ∃ lam₀ : ℕ, ∀ lam : ℕ, lam₀ ≤ lam →
        ∀ F : AvgCaseTI.FieldPres, Fintype.card F.F = 2 ^ (2 * Nat.log 2 lam) →
        ∀ γ : F.F, orderOf γ = Fintype.card F.F - 1 →
          (∀ H : Fin ((2 ^ (2 * Nat.log 2 lam) - 1) / (2 ^ Nat.log 2 lam + 1)) →
              (Fin (2 ^ Nat.log 2 lam + 1) → F.F) → Fin (2 ^ Nat.log 2 lam),
            membershipResources (A.construct ⟨lam, F, γ, canonicalPartition α _⟩).program
              (blockOracle F (A.construct ⟨lam, F, γ, canonicalPartition α _⟩).arity H) ≤
              P.eval lam) ∧
          c ≤ (Fintype.card (Fin ((2 ^ (2 * Nat.log 2 lam) - 1) / (2 ^ Nat.log 2 lam + 1)) →
                (Fin (2 ^ Nat.log 2 lam + 1) → F.F) → Fin (2 ^ Nat.log 2 lam)) : ℝ)⁻¹ *
            ∑ H : Fin ((2 ^ (2 * Nat.log 2 lam) - 1) / (2 ^ Nat.log 2 lam + 1)) →
                (Fin (2 ^ Nat.log 2 lam + 1) → F.F) → Fin (2 ^ Nat.log 2 lam),
              membershipOutputLaw (A.construct ⟨lam, F, γ, canonicalPartition α _⟩).program
                (blockOracle F (A.construct ⟨lam, F, γ, canonicalPartition α _⟩).arity H)
                (fun o => ∃ bits, o = some bits ∧
                  blockSuccess B γ ⌊ρ * ((Fintype.card F.F - 1 : ℕ) : ℝ)⌋₊ (canonicalPartition α _) H
                    (decodeWord F _ (readBits bits)))) ∧
      ∀ Q : Polynomial ℕ, ∃ c' : ℝ, 0 < c' ∧ ∃ lam₁ : ℕ, ∀ lam : ℕ, lam₁ ≤ lam →
        ∀ F : AvgCaseTI.FieldPres, Fintype.card F.F = 2 ^ (2 * Nat.log 2 lam) →
        ∀ γ : F.F, orderOf γ = Fintype.card F.F - 1 →
        ∀ T : QTree (Fin ((2 ^ (2 * Nat.log 2 lam) - 1) / (2 ^ Nat.log 2 lam + 1)) ×
              (Fin (2 ^ Nat.log 2 lam + 1) → F.F)) (Fin (2 ^ Nat.log 2 lam))
            (Fin (Fintype.card F.F - 1) → F.F),
          (∀ H : Fin ((2 ^ (2 * Nat.log 2 lam) - 1) / (2 ^ Nat.log 2 lam + 1)) →
              (Fin (2 ^ Nat.log 2 lam + 1) → F.F) → Fin (2 ^ Nat.log 2 lam),
            T.queries (fun p => H p.1 p.2) ≤ Q.eval lam) →
          (Fintype.card (Fin ((2 ^ (2 * Nat.log 2 lam) - 1) / (2 ^ Nat.log 2 lam + 1)) →
                (Fin (2 ^ Nat.log 2 lam + 1) → F.F) → Fin (2 ^ Nat.log 2 lam)) : ℝ)⁻¹ *
            ∑ H : Fin ((2 ^ (2 * Nat.log 2 lam) - 1) / (2 ^ Nat.log 2 lam + 1)) →
                (Fin (2 ^ Nat.log 2 lam + 1) → F.F) → Fin (2 ^ Nat.log 2 lam),
              (if blockSuccess B γ ⌊ρ * ((Fintype.card F.F - 1 : ℕ) : ℝ)⌋₊ (canonicalPartition α _) H
                  (T.eval fun p => H p.1 p.2) then (1 : ℝ) else 0) ≤
            (2 : ℝ) ^ (-(c' * lam)) := by sorry

end Supplement

end TwoFoldOPI
