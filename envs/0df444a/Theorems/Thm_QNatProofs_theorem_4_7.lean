-- Prove2me | Theorems.Thm_QNatProofs_theorem_4_7
-- name    : QNatProofs.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:05:12.176036+00:00
-- url     : https://prove2.me/theorems/1b21cf9d-8709-4873-90db-91c205c094db
-- title:
--   Theorem 4.7 — main theorem: natural proofs barrier against MH
-- statement:
--   Fix $d_F\ge1$. Let $\mathcal G$ be a classically subexponentially secure PRF family (Definition 3.2) whose functions are computable by polynomial-size depth-$d_F$ threshold circuits. Then there are one QNC$^0$ depth $D$ and a family $\{D_{n,\lambda,T}\}$ such that
--
--   1. $\{D_{n,\lambda,T}\}$ is a PRAL family;
--   2. it is efficiently $e^{-n}$-approximately preparable in $\mathrm{MH}_{8d_F+20}$ (level $8d_F+20$ with depth $D$); and consequently
--   3. no natural promise property is $e^{-n}$-useful against $(\mathrm{MH}_{8d_F+20})_{\mathrm{poly}}$.
--
--   So, assuming subexponentially secure PRFs in TC$^0$, natural proofs cannot prove state-preparation lower bounds against a fixed constant level of the magic hierarchy.
--
--   Differences from the source:
--   - reading: A_kCQ / MH_k (defined in [Par25], not in the paper) → MHLevel k D: C₀Q₁C₁⋯Q_kC_k with Clifford segments C_i of any length and one- and two-qubit unitary segments Q_i of depth ≤ D; reason: the paper's own level counts (p.25: [Cliff][A₄][Cliff][A₄][Cliff] ⊆ A₈; p.40: A₁ = Clifford then QNC⁰) fix this form; A_kCQ ⊆ MH_k on p.22
--   - encoding: MH_{8d_F+20} with constant-depth QNC⁰ segments → MHLevel (8 d_F + 20) D with one D chosen before n, λ, T and the states, the same D in (2) and (3); reason: a depth bound per instance would make level 1 contain every circuit
--   - generalization: Definition 3.2: there is a ∈ (0,1) such that for all sufficiently large m every oracle algorithm B of time ≤ 2^{m^a} has advantage ≤ 2^{−m^a} → ∃ a ∈ (0,1), ∀ uniform oracle algorithm B, ∀ᶠ m, for every auxiliary input z with |z| ≤ m: time ≤ 2^{m^a} on 1^m z → advantage ≤ 2^{−m^a} (IsSecureWithExp); reason: the threshold may depend on B, so the hypothesis is implied by the printed one (where for each large m every algorithm, which may hard-wire z, is covered)
--   - generalization: 𝒢 has uniform keys sampled in poly(m) time and functions evaluated in poly(m) time → KeyedFam: any nonempty finite key sets with the uniform law; no efficiency clauses; reason: weaker hypothesis; no step of the proof samples keys or evaluates 𝒢 classically (the reductions only query the oracle; PRAL needs no efficient sampling, p.9)
--   - generalization: the functions of 𝒢 are computable by polynomial-size depth-d_F threshold circuits → ThresholdComputable: one polynomial p, and for every m and key k some threshold circuit of depth ≤ d_F and size ≤ p(m) computes G_{m,k}; the circuit may depend on the key; reason: weaker hypothesis: a circuit taking the key as input gives these by fixing the key bits; the proof fixes the key (p.33)
--   - generalization: P^yes_n is Haar-measurable → NullMeasurableSet (measurable for the completion of Haar_n); reason: every Borel set qualifies, so more properties are natural and the non-existence statement is stronger
--   - encoding: probability over ψ ← D and the coins of A; A probabilistic polynomial time → Σ_s D{al_T = s}·Pr_coins[A(1^n,1^λ,s) = 1] over the strings s of length T·2^{n+1}; A a CoinAlg with polynomially many coins and one polynomial-time FinTM2 machine (IsPPT), input 1^n0 1^λ0 s; reason: al_T takes finitely many values; a finite sum avoids integrals of possibly non-measurable functions
--   - encoding: a designated n-qubit output register; the other qubits traced out → the first n wires; the partial trace over the remaining wires (reducedOutput); reason: any designation is a renaming of wires, which changes neither size nor level
--   - reading: al_T(ψ): polar coordinates written to T fractional bits → QNatProofs.al: basis strings in increasing binary order, r-bits then θ-bits, truncation ⌊2^T r⌋ capped at 2^T−1 (so r = 1 is written 1⋯1), θ = arg/(2π) mod 1 with θ(0) = 0; reason: the printed codomain {0,1}^{2T·2^n} forces the cap; the order and θ(0) are unspecified on p.8
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), Theorem 4.7, p.33; proof p.33

import Mathlib
import Definitions.Def_QNatProofs_MHLevel
import Definitions.Def_QNatProofs_IsPRAL
import Definitions.Def_QNatProofs_ThrCircuit

set_option autoImplicit false

namespace QNatProofs

/-- **Theorem 4.7 (Main theorem: natural proofs barrier against MH)** (Li, Parham, *Natural proofs
for quantum state preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.33):
"Fix a constant `d_F ≥ 1`. Suppose there exists a classically subexponentially secure PRF family
`𝒢` in the sense of Definition 3.2, whose functions are computable by polynomial-size depth-`d_F`
threshold circuits. Then there exists a PRAL family that is efficiently `e^{-n}`-approximately
`MH_{8d_F+20}`-preparable. Consequently, no natural promise property is `e^{-n}`-useful against
`(MH_{8d_F+20})_poly`."

**Formalization Note** `MH_k` is `MHLevel k D`: Clifford segments alternating with `k` segments of
one- and two-qubit gates of depth at most `D`, with one depth bound `D` for the whole statement.
Security is against uniform oracle algorithms (`KeyedFam.IsClassicalSubexpSecure`); the threshold
circuits may depend on the key. -/
theorem theorem_4_7 (dF : ℕ) (hdF : 1 ≤ dF) (G : KeyedFam) (hsec : G.IsClassicalSubexpSecure)
    (hthr : G.ThresholdComputable dF) :
    ∃ (D : ℕ) (𝒟 : PRALFamilyData), IsPRAL 𝒟 ∧
      EffApproxPreparable 𝒟 (MHLevel (8 * dF + 20) D) (fun n => Real.exp (-(n : ℝ))) ∧
      ¬ ∃ P : PromiseProperty, P.IsNatural ∧
        P.IsUseful (MHLevel (8 * dF + 20) D) (fun n => Real.exp (-(n : ℝ))) := by sorry

end QNatProofs
