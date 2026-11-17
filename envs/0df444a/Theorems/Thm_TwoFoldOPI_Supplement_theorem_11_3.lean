-- Prove2me | Theorems.Thm_TwoFoldOPI_Supplement_theorem_11_3
-- name    : TwoFoldOPI.Supplement.theorem_11_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:11:42.443988+00:00
-- url     : https://prove2.me/theorems/f9b39f16-ccc7-459a-bb77-3d580b9260dd
-- title:
--   Theorem 11.3 — quantum algorithm in the oracle model
-- statement:
--   Let the load data of $\mathcal D_\lambda$ be admissible with $\eta=1$, and suppose the rate $\rho$ of $C_\lambda$ satisfies
--   $$\rho>1-\Pr[K_{\mathrm{src}}-1\in B_{I_{\mathrm{src}}}]\cdot\Pr[K_{\mathrm{tar}}+1\in B_{I_{\mathrm{tar}}}].$$
--   Here $\ell=\lfloor\log_2\lambda\rfloor$, $q=2^{2\ell}$, $M=q-1$, $s=2^{\ell}+1$, $n=2^{\ell}$, $m=M/s$, $C_\lambda=\mathrm{RS}_{\mathbb F_q,\gamma,\lfloor\rho M\rfloor}$ grouped into $m$ blocks of $s$ symbols, and an instance gives oracle access to independent uniformly random $H_1,\dots,H_m:\mathbb F_q^s\to[n]$. Then there is a uniform quantum algorithm which, for all sufficiently large $\lambda$, runs in time $\mathrm{poly}(\lambda)$, makes $\mathrm{poly}(\lambda)$ queries to the $H_i$, and outputs an element of $C_\lambda\cap A_{H_1,\dots,H_m}$ with probability $\Omega(1)$ over $H_1,\dots,H_m$ and its internal randomness.
--
--   This is the completeness half of the oracle separation for load constraints (Theorem 11.9).
--
--   Differences from the source:
--   - generalization: an explicitly represented F_q and an arbitrary generator γ → the guarantee holds for every explicit presentation of F_q and every generator γ; reason: specializes to any fixed choice
--   - reading: public descriptions of C_λ, the partition and the truncated-load membership circuits → public input (λ, F, γ, class map of the partition of Definition 11.2); the membership circuits are not input; reason: for fixed admissible load data a uniform algorithm produces the circuits itself with the fixed admissibility program; the partition is input because ⌊α_r n⌋ need not be computable
--   - encoding: time poly(λ), poly(λ) queries, success Ω(1), for all sufficiently large λ → charged resources (gates, qubits, queries, all operations) at most P(λ) on every oracle tuple; success at least a constant c > 0 for all λ ≥ λ₀; reason: explicit quantifiers for the asymptotic notation
--   - encoding: quantum oracle access to the H_i → m oracles evaluating H_i reversibly on s·b + ⌈log₂ n⌉ qubits (blockOracle); a failure leaf counts as failure; reason: the paper's reversible-evaluation convention in the base mission's bit layout
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11.1, Theorem 11.3, p. 57

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
import Definitions.Def_QAlgorithms_Defs_OPIUniformity
import Definitions.Def_TwoFoldOPI_elemBits
import Definitions.Def_TwoFoldOPI_decodeWord
import Definitions.Def_TwoFoldOPI_Supplement_readBits
import Definitions.Def_TwoFoldOPI_Supplement_Admissible
import Definitions.Def_TwoFoldOPI_Supplement_pStay
import Definitions.Def_TwoFoldOPI_Supplement_canonicalPartition
import Definitions.Def_TwoFoldOPI_Supplement_DLamInput
import Definitions.Def_TwoFoldOPI_Supplement_blockOracle
import Definitions.Def_TwoFoldOPI_Supplement_blockSuccess

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms QAlgorithms.OPI

/-- **Theorem 11.3 (quantum algorithm in the oracle model).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11.1, Theorem 11.3, p.57: "Assume the load data of D_λ are admissible (Definition 10.9)
with η = 1. With the notation from Theorem 10.11, suppose that the rate parameter ρ of C_λ
(Definition 11.1) satisfies ρ > 1 − Pr[K_src − 1 ∈ B_{I_src}] · Pr[K_tar + 1 ∈ B_{I_tar}]. There is
a uniform quantum algorithm which, for all sufficiently large λ and given an oracle-represented
instance sampled from D_λ, runs in time poly(λ) and makes poly(λ) queries to the H_i's. Its success
probability over the randomness of H_1, …, H_m and the algorithm's internal randomness is Ω(1).";
Definitions 11.1–11.2, p.57.

With `ℓ = ⌊log₂ λ⌋`, `q = 2^{2ℓ}`, `M = q − 1`, `s = 2^ℓ + 1`, `n = 2^ℓ`, `m = M/s`,
`k = ⌊ρM⌋`: there are a uniform quantum algorithm `A` (`m` oracles, each on a block of `s` symbols
plus `⌈log₂ n⌉` answer qubits; output: `M` symbols), a polynomial `P`, a constant `c > 0` and
`lam₀` such that for all `λ ≥ lam₀`, every field presentation `F` of order `q`, every generator `γ` of
`F^*`, on the public data `(λ, F, γ, S_1, …, S_R)` (the partition of Definition 11.2):
1. for every tuple of functions `H_i : F^s → [n]`, the charged resources (time and queries) are at
   most `P(λ)`;
2. averaged over independent uniform `H_1, …, H_m`, the probability that `A` outputs
   `x ∈ C_λ ∩ A_{H_1,…,H_m}` (`C_λ = RS_{F,γ,k}`, load set with `B_a = B_r` for `a ∈ S_r`) is `≥ c`.

**Formalization Note.** `Ω(1)` is one `c > 0`; "for all sufficiently large λ" is `lam₀`; `poly(λ)` is
`P`, chosen before `λ`. The algorithm is a `QAlgorithms.OPI.UniformResourceFamily` on the public
data `DLamInput` (Clifford+T, measurements, coins), with quantum oracle access `blockOracle` to the
`H_i` (reversible evaluation, p.26); its charged resources include every query and gate. The claim is
made for every explicit presentation of `F_q` and every generator `γ` ("an arbitrary generator").
The membership circuits of Definition 11.2 are not input: the fixed admissibility program produces
them. `p_stay` is `pStay` with `η = 1`. -/
theorem theorem_11_3 {R : ℕ} [NeZero R] (B : Fin R → Set ℕ) (α : Fin R → ℝ) (ν : ℝ)
    (hadm : Admissible B α 1 ν) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρ : 1 - pStay B α 1 ν < ρ) :
    ∃ A : UniformResourceFamily (DLamInput R) DLamInput.encode DLamInput.scale,
      (∀ x : DLamInput R,
        (A.construct x).oracles = (2 ^ (2 * Nat.log 2 x.lam) - 1) / (2 ^ Nat.log 2 x.lam + 1) ∧
        (∀ k, (A.construct x).arity k = (2 ^ Nat.log 2 x.lam + 1) * bitsPerSymbol x.F +
          Nat.clog 2 (2 ^ Nat.log 2 x.lam)) ∧
        (A.construct x).outputBits = (Fintype.card x.F.F - 1) * bitsPerSymbol x.F) ∧
      ∃ (P : Polynomial ℕ) (c : ℝ), 0 < c ∧ ∃ lam₀ : ℕ, ∀ lam : ℕ, lam₀ ≤ lam →
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
                    (decodeWord F _ (readBits bits))) := by sorry

end Supplement

end TwoFoldOPI
