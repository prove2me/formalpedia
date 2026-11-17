-- Prove2me | Theorems.Thm_TwoFoldOPI_Supplement_theorem_12_2
-- name    : TwoFoldOPI.Supplement.theorem_12_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:14:31.544649+00:00
-- url     : https://prove2.me/theorems/15fa78b6-fb75-47ac-ae92-591b91058708
-- title:
--   Theorem 12.2 — plain-model ordinary-RS algorithms
-- statement:
--   Let the load data be admissible with $\eta=1$ and let $p_{\mathrm{stay}}=\Pr[K_{\mathrm{src}}-1\in B_{I_{\mathrm{src}}}]\Pr[K_{\mathrm{tar}}+1\in B_{I_{\mathrm{tar}}}]$. For the instances of Definition 12.1 — $m=q-1$, $n=q$, $C_q=\mathrm{RS}_{\mathbb F_q,\gamma,\lfloor\rho m\rfloor}$ for a fixed rational rate $\rho\in(0,1)$, a partition of $[n]$ with $|S_r|=\alpha_rn+O(1)$, and the complete truth tables of independent uniformly random bijections $\pi_1,\dots,\pi_m:\mathbb F_q\to[n]$ — the following hold for all sufficiently large $q$:
--   1. if $q$ is prime and $\rho>1-p_{\mathrm{stay}}$, a uniform quantum algorithm runs in time $\mathrm{poly}(q)$ and outputs an element of $C_q\cap A_{\pi_1,\dots,\pi_m}$ with probability at least $q^{-O(1)}$;
--   2. for every prime power $q$, if $\rho>1-p_{\mathrm{stay}}^2$, a uniform quantum algorithm runs in time $\mathrm{poly}(q)$ and outputs such an element with probability $\Omega(1)$.
--
--   Both probabilities are over the random truth tables and the algorithm's randomness; the exponents and success bounds may depend on the rate and the load data. A purported output can be verified deterministically in time $\mathrm{poly}(q)$.
--
--   These are plain-model versions of the oracle algorithm of Theorem 11.3, with ordinary Reed–Solomon codes and no oracle.
--
--   Differences from the source:
--   - generalization: an explicitly represented F_q and an explicitly specified generator γ → the claims hold for every explicit presentation of F_q and every generator γ; reason: specializes to any fixed choice
--   - reading: the polynomial exponents and success bounds may depend on the fixed rate and load data; partition with |S_r| = α_r n + O(1) → the algorithm, the polynomial P and the exponent e (resp. the constant c) are chosen before the bound b of the partition; only the threshold q₀ depends on b; reason: the stated dependence of the constants; the threshold absorbs the O(1) bound
--   - encoding: time poly(q), success q^{−O(1)}, success Ω(1), for all sufficiently large q → charged resources at most P(q); success at least q^{−e} for one e ∈ ℕ (resp. at least c > 0); for all q ≥ q₀; reason: explicit quantifiers for the asymptotic notation
--   - encoding: uniformly random balanced functions π_i : F_q → [n] given by truth tables → uniform random bijections F ≃ Fin q, written as tables in the input encoding; reason: with |F_q| = n = q, balanced functions are exactly bijections (Definition 12.1)
--   - generalization: running time on the instances of Definition 12.1; verification of a purported output → the running-time bound holds for every table input, and the verifier is correct for every q, every partition and every table; reason: specializes to the instances of Definition 12.1
--   - reading: the truncated-load membership circuits are public parts of the instance → not input; produced by the fixed admissibility program; reason: for fixed admissible load data a uniform algorithm computes them itself in polynomial time
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §12, Theorem 12.2, p. 65

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIBitPrograms
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
import Definitions.Def_QAlgorithms_Defs_OPIUniformity
import Definitions.Def_TwoFoldOPI_elemBits
import Definitions.Def_TwoFoldOPI_decodeWord
import Definitions.Def_TwoFoldOPI_Supplement_readBits
import Definitions.Def_TwoFoldOPI_Supplement_Admissible
import Definitions.Def_TwoFoldOPI_Supplement_pStay
import Definitions.Def_TwoFoldOPI_Supplement_PlainInput
import Definitions.Def_TwoFoldOPI_Supplement_blockSuccess

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms QAlgorithms.OPI

/-- **Theorem 12.2 (plain-model ordinary-RS algorithms).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §12, Theorem 12.2, p.65: "Use the random variables from Theorem 10.11, and define
p_stay = Pr[K_src − 1 ∈ B_{I_src}] Pr[K_tar + 1 ∈ B_{I_tar}]. For the instances in Definition 12.1,
with rate parameter ρ, the following hold for all sufficiently large q: (i) If q is prime and
ρ > 1 − p_stay, a uniform quantum algorithm runs in time poly(q) and outputs an element of
C_q ∩ A_{π_1,…,π_m} with probability at least q^{−O(1)}. (ii) For every prime power q, if
ρ > 1 − p_stay², a uniform quantum algorithm runs in time poly(q) and outputs such an element with
probability Ω(1). Both probabilities are over the random public truth tables and the algorithm's
internal randomness. The polynomial exponents and success bounds may depend on the fixed rate and
load data. A purported output can be verified deterministically in time poly(q)."; Definition
12.1, pp.64–65 (admissible load data with η = 1; m = q − 1, n = q, k = ⌊ρm⌋, fixed rational
ρ ∈ (0, 1); C_q = RS_{F_q,γ,k}; partition with |S_r| = α_r n + O(1); uniformly random balanced
π_1, …, π_m : F_q → [n], i.e. uniformly random bijections, given by complete truth tables).

With `q = |F|`, `m = q − 1`, `n = q`, `k = ⌊ρm⌋`, success means `x ∈ RS_{F,γ,k}` and
`(π_1(x_1), …, π_m(x_m)) ∈ T` (`blockSuccess` with `s = 1`).
1. If `ρ > 1 − p_stay`: there are a uniform quantum algorithm `A`, a polynomial `P` and an exponent
   `e` such that for every bound `b` there is `q₀` with: for every prime `q ≥ q₀`, presentation `F`
   of `F_q`, generator `γ` and partition with `| |S_r| − α_r q | ≤ b`, the resources are at most
   `P(q)` on every input, and the success probability averaged over uniform bijections
   `π_1, …, π_m` is at least `q^{−e}`.
2. If `ρ > 1 − p_stay²`: the same with every prime power `q ≥ q₀` and success at least a constant
   `c > 0`.
3. There is a deterministic bit program `V` and a polynomial `P` such that on every instance (any
   `q`, any generator `γ`, any partition and tables) and every candidate of `m` symbols, `V` halts
   within `P(q)` transitions and accepts exactly when the candidate is a success.

**Formalization Note.** `q^{−O(1)}` is `q^{−e}`, `Ω(1)` is `c > 0`, `poly(q)` is `P`; the algorithm, `P`, `e`
and `c` are chosen before the partition bound `b` (they may depend on `ρ` and the load data only),
and `q₀` after `b`. Algorithms are `QAlgorithms.OPI.UniformResourceFamily`s on `PlainInput` with no
oracle: the truth tables are ordinary input. The claim is for every explicit presentation of `F_q`
and every generator. The membership circuits are produced by the fixed admissibility program and
are not input. Verification (clause 3) is stated for all `q` and all tables, which includes the
instances of Definition 12.1. `ρ` is rational, as in Definition 12.1. -/
theorem theorem_12_2 {R : ℕ} (B : Fin R → Set ℕ) (α : Fin R → ℝ) (ν : ℝ)
    (hadm : Admissible B α 1 ν) (ρ : ℚ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    (1 - pStay B α 1 ν < ρ →
      ∃ A : UniformResourceFamily (PlainInput R) PlainInput.encode PlainInput.scale,
        (∀ x : PlainInput R, (A.construct x).oracles = 0 ∧
          (A.construct x).outputBits = (Fintype.card x.F.F - 1) * bitsPerSymbol x.F) ∧
        ∃ (P : Polynomial ℕ) (e : ℕ), ∀ b : ℝ, ∃ q₀ : ℕ,
          ∀ F : AvgCaseTI.FieldPres, q₀ ≤ Fintype.card F.F → (Fintype.card F.F).Prime →
          ∀ γ : F.F, orderOf γ = Fintype.card F.F - 1 →
          ∀ part : Fin (Fintype.card F.F) → Fin R,
            (∀ r, |((Finset.univ.filter fun a => part a = r).card : ℝ) -
              α r * Fintype.card F.F| ≤ b) →
            (∀ π : Fin (Fintype.card F.F - 1) → F.F → Fin (Fintype.card F.F),
              membershipResources (A.construct ⟨F, γ, part, π⟩).program (fun _ => 1) ≤
                P.eval (Fintype.card F.F)) ∧
            ((Fintype.card F.F : ℝ) ^ e)⁻¹ ≤
              (Fintype.card (Fin (Fintype.card F.F - 1) → (F.F ≃ Fin (Fintype.card F.F))) : ℝ)⁻¹ *
                ∑ π : Fin (Fintype.card F.F - 1) → (F.F ≃ Fin (Fintype.card F.F)),
                  membershipOutputLaw (A.construct ⟨F, γ, part, fun i => π i⟩).program (fun _ => 1)
                    (fun o => ∃ bits, o = some bits ∧
                      blockSuccess (s := 1) B γ ⌊(ρ : ℝ) * ((Fintype.card F.F - 1 : ℕ) : ℝ)⌋₊ part
                        (fun i blk => π i (blk 0)) (decodeWord F _ (readBits bits)))) ∧
    (1 - pStay B α 1 ν ^ 2 < ρ →
      ∃ A : UniformResourceFamily (PlainInput R) PlainInput.encode PlainInput.scale,
        (∀ x : PlainInput R, (A.construct x).oracles = 0 ∧
          (A.construct x).outputBits = (Fintype.card x.F.F - 1) * bitsPerSymbol x.F) ∧
        ∃ (P : Polynomial ℕ) (c : ℝ), 0 < c ∧ ∀ b : ℝ, ∃ q₀ : ℕ,
          ∀ F : AvgCaseTI.FieldPres, q₀ ≤ Fintype.card F.F →
          ∀ γ : F.F, orderOf γ = Fintype.card F.F - 1 →
          ∀ part : Fin (Fintype.card F.F) → Fin R,
            (∀ r, |((Finset.univ.filter fun a => part a = r).card : ℝ) -
              α r * Fintype.card F.F| ≤ b) →
            (∀ π : Fin (Fintype.card F.F - 1) → F.F → Fin (Fintype.card F.F),
              membershipResources (A.construct ⟨F, γ, part, π⟩).program (fun _ => 1) ≤
                P.eval (Fintype.card F.F)) ∧
            c ≤ (Fintype.card (Fin (Fintype.card F.F - 1) → (F.F ≃ Fin (Fintype.card F.F))) : ℝ)⁻¹ *
                ∑ π : Fin (Fintype.card F.F - 1) → (F.F ≃ Fin (Fintype.card F.F)),
                  membershipOutputLaw (A.construct ⟨F, γ, part, fun i => π i⟩).program (fun _ => 1)
                    (fun o => ∃ bits, o = some bits ∧
                      blockSuccess (s := 1) B γ ⌊(ρ : ℝ) * ((Fintype.card F.F - 1 : ℕ) : ℝ)⌋₊ part
                        (fun i blk => π i (blk 0)) (decodeWord F _ (readBits bits)))) ∧
    ∃ (V : BitOracleProgram) (P : Polynomial ℕ), (∀ op ∈ V.code, ∀ t, op ≠ BitInstruction.coin t) ∧
      ∀ (x : PlainInput R), orderOf x.γ = Fintype.card x.F.F - 1 →
      ∀ bits : Fin ((Fintype.card x.F.F - 1) * bitsPerSymbol x.F) → Bool,
        (bitProgramExecution V (x.encode ++ List.ofFn bits) (fun _ => false) (fun _ => false)
          (P.eval (Fintype.card x.F.F))).status.isSome ∧
        ((bitProgramExecution V (x.encode ++ List.ofFn bits) (fun _ => false) (fun _ => false)
          (P.eval (Fintype.card x.F.F))).status = some true ↔
          blockSuccess (s := 1) B x.γ ⌊(ρ : ℝ) * ((Fintype.card x.F.F - 1 : ℕ) : ℝ)⌋₊ x.part
            (fun i blk => x.π i (blk 0)) (decodeWord x.F _ bits)) := by sorry

end Supplement

end TwoFoldOPI
