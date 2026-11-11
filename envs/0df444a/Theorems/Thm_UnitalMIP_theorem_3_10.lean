-- Prove2me | Theorems.Thm_UnitalMIP_theorem_3_10
-- name    : UnitalMIP.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:41:14.529243+00:00
-- url     : https://prove2.me/theorems/6b78fc1b-07cb-413e-bd65-12166eb3f5da
-- title:
--   Theorem 3.10 — $\mathrm{RE}\subseteq\mathrm{MIP}^{\Psi_\lambda}[\mathrm{poly},O(1)]$ for $0<\lambda\le1$
-- statement:
--   For every fixed $0<\lambda\le1$, with the boundary canonical form $\Psi_\lambda$,
--
--   $$
--   \mathrm{RE}\subseteq\mathrm{MIP}^{\Psi_\lambda}[\mathrm{poly},O(1)].
--   $$
--
--   As a corollary, $\mathrm{RE}\subseteq\mathrm{MIP}^\psi[\mathrm{poly},O(1)]$ for every entangled $\psi\in M_2\otimes M_2$ with maximally mixed marginals and $\rho_{\max}(\psi)=1$.
--
--   This is the lower bound of the second branch: these noisy states keep the full power of MIP* = RE.
--
--   **Formalization Note** Both clauses are stated. No computability of $\psi$ is assumed: the statement and proof do not use it.
--
--   Differences from the source:
--   - reading: Definition 2.15: a uniform family of one-round protocols with a classical randomized verifier that samples question pairs and evaluates decision predicates in time polynomial in the input bit length (prose) → the published `MIPRE.PolyVerifier`, efficient on every input: closed sampler and decider programs, seed length and question length at most $P(|z|)$, decider time polynomial in the total input length, strings longer than $P(|z|)$ rejected; reason: the source defines the class in prose; this is the published machine model of the same polynomial-time two-prover one-round verifier, and it imposes no condition on the language
--   - reading: a constant completeness–soundness gap → fixed real constants $s<c$, independent of the input, with $z\in L\Rightarrow\omega^*_\infty(G_z,\psi)\ge c$ and $z\notin L\Rightarrow\omega^*_\infty(G_z,\psi)\le s$; reason: the source's proofs use exactly this form (proof of Theorem 3.11, p.75: completeness $c$, soundness $s<c$; §4.5, p.65); input-dependent thresholds would not be a constant gap
--   - encoding: answers of length at most $a(|z|)$ → the decider rejects whenever an answer is longer than $a(|z|)$ bits; reason: a strategy can map every overlong answer to a short one without lowering its value, so the value is that of the game with answers of length at most $a(|z|)$
--   - encoding: $\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]$ and $\mathrm{MIP}^\psi[\mathrm{poly},O(1)]$ → some polynomial (resp. one constant) bounds the answer length; questions are bounded by the verifier's polynomial; reason: same classes
--   - encoding: equalities and inclusions of complexity classes → `∀ L, _ ↔ _` (resp. `∀ L, _ → _`) on languages $L\subseteq\{0,1\}^*$; reason: same statements
--   - encoding: $\rho_{\max}$ as a maximum (Definition 2.20) → `sSup` of the set of admissible values $|\mathrm{Tr}[\psi(X\otimes Y^\dagger)]|$; reason: the set is nonempty and bounded and the maximum is attained by compactness, so the supremum equals it
--   - encoding: $\psi^{\otimes n}$ → `tensorPow ψ n`: the same operator with Alice's $n$ registers collected first; reason: a permutation of tensor factors; Alice holds the first qubit of every copy, as in the source
--   - generalization: the §1.1 standing assumption (“Throughout, let ψ be a fixed two-qubit state … and assume that its entries are computable in polynomial time”, p.4) → every real $\lambda\in(0,1]$ and every entangled two-qubit ψ with maximally mixed marginals and $\rho_{\max}(\psi)=1$, with no computability hypothesis; reason: the proof (p.74) hard-codes a rational $\lambda'\le\lambda$ and only constants depending on it, so it does not use the entries of the state; it specializes to the source's claim on every computable state
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Theorem 3.10, p.31; proof, p.74

import Mathlib
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals
import Definitions.Def_UnitalMIP_rhoMax
import Definitions.Def_UnitalMIP_canonicalState
import Definitions.Def_UnitalMIP_MIPPsi

open scoped Matrix

namespace UnitalMIP

/-- **Theorem 3.10** (RE lower bound; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.31; proved p.74). For every fixed `0 < λ ≤ 1`,
`RE ⊆ MIP^{Ψ_λ}[poly, O(1)]`. As a corollary, `RE ⊆ MIP^ψ[poly, O(1)]` for every entangled
`ψ ∈ M₂ ⊗ M₂` with maximally mixed marginals and `ρmax(ψ) = 1`.

**Formalization Note** Both clauses are stated. No computability of `ψ` is assumed: the source's
statement and proof do not use it (the proof hard-codes a rational `λ' ≤ λ`). -/
theorem theorem_3_10 :
    (∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ L, MIPRE.IsRE L → MIPPsiPolyConst (PsiBoundary lam) L) ∧
      ∀ (ψ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ), HasMaxMixedMarginals ψ →
        IsEntangled ψ → rhoMax ψ = 1 → ∀ L, MIPRE.IsRE L → MIPPsiPolyConst ψ L := by sorry

end UnitalMIP
