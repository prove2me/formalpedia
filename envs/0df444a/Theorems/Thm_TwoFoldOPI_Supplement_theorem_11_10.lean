-- Prove2me | Theorems.Thm_TwoFoldOPI_Supplement_theorem_11_10
-- name    : TwoFoldOPI.Supplement.theorem_11_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:13:24.870509+00:00
-- url     : https://prove2.me/theorems/92447d5d-ab37-44f5-a6f8-14bce39ccdb6
-- title:
--   Theorem 11.10 — proof of quantumness with worst-case completeness
-- statement:
--   Under the hypotheses of Theorem 11.9 there is a keyless noninteractive publicly verifiable protocol relative to a random oracle such that:
--   1. for every fixed oracle, the honest quantum prover is accepted with probability $1-\mathrm{negl}(\lambda)$;
--   2. for a uniformly random oracle, every computationally unbounded classical prover making polynomially many classical queries is accepted with probability at most $\mathrm{negl}(\lambda)$.
--
--   Here $f(\lambda)=\mathrm{negl}(\lambda)$ means that for every constant $c>0$, $f(\lambda)\le\lambda^{-c}$ for all sufficiently large $\lambda$. The honest prover is an efficient quantum algorithm and the verifier an efficient classical algorithm with oracle access.
--
--   This upgrades the average-case completeness of Theorem 11.9 to completeness for every fixed oracle.
--
--   Differences from the source:
--   - reading: a keyless noninteractive publicly verifiable protocol relative to a random oracle → a PoQProtocol: a Boolean random oracle on inLen(λ)-bit strings; the honest prover a uniform family of quantum programs on input λ with polynomially bounded charged resources; the verifier a classical bit program on (λ, message) with classical queries, halting within a polynomial in λ + |msg| transitions; reason: the paper does not fix a machine model; Boolean oracles lose no generality
--   - generalization: a classical verifier → a deterministic classical verifier (no coin instructions); reason: the protocol's verifier is deterministic; requiring it only strengthens the existential claim
--   - encoding: 1 − negl(λ) for every fixed oracle; at most negl(λ) for every poly-query classical prover → for every c > 0 there is λ₀ with the bound λ^{−c} for all λ ≥ λ₀, every oracle (resp. every prover with at most Q(λ) queries, for every polynomial Q); reason: the definition of negl on p.20; taking the worst oracle or prover at each λ shows the uniform form is equivalent
--   - encoding: every computationally unbounded classical prover → every deterministic query tree; reason: randomized provers are mixtures of deterministic trees
--   - encoding: Suppose 1 − p_stay < min{τ, 1} → not repeated; reason: implied by the choice of ρ
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11.4, Theorem 11.10, p. 62

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
import Definitions.Def_QAlgorithms_Defs_OPIUniformity
import Definitions.Def_TwoFoldOPI_Supplement_Admissible
import Definitions.Def_TwoFoldOPI_Supplement_pStay
import Definitions.Def_TwoFoldOPI_Supplement_tailThreshold
import Definitions.Def_TwoFoldOPI_Supplement_QTree
import Definitions.Def_TwoFoldOPI_Supplement_PoQProtocol

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms QAlgorithms.OPI

open Classical in
/-- **Theorem 11.10 (proof of quantumness with worst-case completeness).**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11.4, Theorem 11.10, p.62: "Under the hypotheses of Theorem 11.9, there is a keyless
noninteractive publicly verifiable protocol relative to a random oracle with the following
properties. For every fixed oracle, the honest quantum prover is accepted with probability
1 − negl(λ). For a uniformly random oracle, every computationally unbounded classical prover making
polynomially many classical queries is accepted with probability at most negl(λ)."; Notation, p.20:
"f(n) = negl(n) to mean f(n) = n^{−ω(1)}: for every constant c > 0, there is an n_0 such that
f(n) ≤ n^{−c} for all n ≥ n_0."; §11.3, p.61 ("a classical verifier accepts an efficient quantum
prover … Our protocols are noninteractive, publicly verifiable, and keyless").

Under the hypotheses of Theorem 11.9 there is a protocol `Π` (`PoQProtocol`: oracle input length,
honest quantum prover, classical verifier, verifier time bound) such that:
1. the verifier is deterministic (no coin instruction) and halts within `vtime(λ + |msg|)`
   transitions on every message and every oracle;
2. the honest prover uses at most `P(λ)` charged resources for one polynomial `P`, on every oracle;
3. (completeness) for every `c > 0` there is `λ₀` such that for all `λ ≥ λ₀` and every oracle `H`,
   the honest prover's message is accepted with probability `≥ 1 − λ^{−c}`;
4. (soundness) for every polynomial `Q` and every `c > 0` there is `λ₀` such that for all
   `λ ≥ λ₀` and every classical prover `T` (a query tree) making at most `Q(λ)` queries on every
   oracle, its message is accepted with probability `≤ λ^{−c}` over a uniform oracle `H`.

**Formalization Note.** `negl(λ)` is the definition of p.20; a bound `λ^{−c}` for every `c` and
every prover (resp. oracle) at each `λ` is the same as negligibility for every prover family (resp.
fixed oracle), since the worst case at each `λ` forms such a family. The honest prover is a
`QAlgorithms.OPI.UniformResourceFamily` on input `λ` (uniform, polynomial time) with quantum
access to `H`; the verifier is a classical bit program with classical queries; together they make
the protocol noninteractive (one message), keyless (no setup) and publicly verifiable (no secret).
A classical prover is a deterministic query tree (unbounded local computation); randomized provers
are mixtures. The random oracle is a uniformly random Boolean function on `inLen λ`-bit strings
(`PoQProtocol`). The protocol is existential, as printed; the hypotheses are those of Theorem 11.9
(the hypothesis `1 − p_stay < min{τ, 1}` is implied by the choice of `ρ`). -/
theorem theorem_11_10 {R : ℕ} [NeZero R] (B : Fin R → Set ℕ) (α : Fin R → ℝ) (ν : ℝ)
    (hadm : Admissible B α 1 ν) (ρ : ℝ) (hρ0 : 0 < ρ) (hgap : 1 - pStay B α 1 ν < ρ)
    (hρ1 : ρ < 1) (hτ : ENNReal.ofReal ρ < weightedTail B α) :
    ∃ Pr : PoQProtocol,
      (∀ op ∈ Pr.verifier.code, ∀ t, op ≠ BitInstruction.coin t) ∧
      (∀ (lam : ℕ) (H : (Fin (Pr.inLen lam) → Bool) → Bool) (msg : List Bool),
        (bitProgramExecution Pr.verifier (LocalHamiltonian.encBin lam ++ msg)
          (Pr.verifierOracle lam H) (fun _ => false)
          (Pr.vtime.eval (lam + msg.length))).status.isSome) ∧
      (∃ P : Polynomial ℕ, ∀ (lam : ℕ) (H : (Fin (Pr.inLen lam) → Bool) → Bool),
        membershipResources (Pr.prover.construct lam).program (Pr.proverOracle lam H) ≤
          P.eval lam) ∧
      (∀ c : ℝ, 0 < c → ∃ lam₀ : ℕ, ∀ lam : ℕ, lam₀ ≤ lam →
        ∀ H : (Fin (Pr.inLen lam) → Bool) → Bool,
          1 - (lam : ℝ) ^ (-c) ≤
            membershipOutputLaw (Pr.prover.construct lam).program (Pr.proverOracle lam H)
              (fun o => ∃ bits, o = some bits ∧ Pr.accepts lam H (List.ofFn bits))) ∧
      ∀ (Q : Polynomial ℕ) (c : ℝ), 0 < c → ∃ lam₀ : ℕ, ∀ lam : ℕ, lam₀ ≤ lam →
        ∀ T : QTree (Fin (Pr.inLen lam) → Bool) Bool (List Bool),
          (∀ H : (Fin (Pr.inLen lam) → Bool) → Bool, T.queries H ≤ Q.eval lam) →
          (Fintype.card ((Fin (Pr.inLen lam) → Bool) → Bool) : ℝ)⁻¹ *
            ∑ H : (Fin (Pr.inLen lam) → Bool) → Bool,
              (if Pr.accepts lam H (T.eval H) then (1 : ℝ) else 0) ≤ (lam : ℝ) ^ (-c) := by sorry

end Supplement

end TwoFoldOPI
