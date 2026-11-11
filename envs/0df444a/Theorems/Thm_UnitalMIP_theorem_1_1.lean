-- Prove2me | Theorems.Thm_UnitalMIP_theorem_1_1
-- name    : UnitalMIP.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:41:18.766626+00:00
-- url     : https://prove2.me/theorems/44b8b828-9c52-4274-a9e6-28d08378da0f
-- title:
--   Theorem 1.1 — $\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]$ is NEXP = MIP if $\psi$ is separable or $\rho_{\max}(\psi)<1$, RE if entangled with $\rho_{\max}(\psi)=1$
-- statement:
--   Let $\psi\in M_2\otimes M_2$ be a fixed two-qubit state with maximally mixed marginals, whose entries are computable in polynomial time (the standing assumption of §1.1).
--
--   1. If $\psi$ is separable or $\rho_{\max}(\psi)<1$, then
--   $$
--   \mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]=\mathrm{NEXP}=\mathrm{MIP}.
--   $$
--   2. If $\psi$ is entangled and $\rho_{\max}(\psi)=1$, then
--   $$
--   \mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]=\mathrm{RE}.
--   $$
--
--   Here $\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]$ is the class of languages with two-prover one-round protocols with polynomial-length questions and answers in which the provers share any finite number of copies of $\psi$ and nothing else. The theorem classifies completely the power of an EPR pair subjected to unital qubit noise: the answer depends jointly on the maximal correlation and on entanglement.
--
--   **Formalization Note** The computability hypothesis is the paper's own standing assumption ("Throughout, … assume that its entries are computable in polynomial time", §1.1, p.4), stated as a hypothesis. Classes are predicates on languages and each equality is `∀ L, _ ↔ _`. MIP is the general classical multi-prover class; RE is the published `MIPRE.IsRE`.
--
--   Differences from the source:
--   - reading: Definition 2.15: a uniform family of one-round protocols with a classical randomized verifier that samples question pairs and evaluates decision predicates in time polynomial in the input bit length (prose) → the published `MIPRE.PolyVerifier`, efficient on every input: closed sampler and decider programs, seed length and question length at most $P(|z|)$, decider time polynomial in the total input length, strings longer than $P(|z|)$ rejected; reason: the source defines the class in prose; this is the published machine model of the same polynomial-time two-prover one-round verifier, and it imposes no condition on the language
--   - reading: a constant completeness–soundness gap → fixed real constants $s<c$, independent of the input, with $z\in L\Rightarrow\omega^*_\infty(G_z,\psi)\ge c$ and $z\notin L\Rightarrow\omega^*_\infty(G_z,\psi)\le s$; reason: the source's proofs use exactly this form (proof of Theorem 3.11, p.75: completeness $c$, soundness $s<c$; §4.5, p.65); input-dependent thresholds would not be a constant gap
--   - encoding: answers of length at most $a(|z|)$ → the decider rejects whenever an answer is longer than $a(|z|)$ bits; reason: a strategy can map every overlong answer to a short one without lowering its value, so the value is that of the game with answers of length at most $a(|z|)$
--   - encoding: $\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]$ and $\mathrm{MIP}^\psi[\mathrm{poly},O(1)]$ → some polynomial (resp. one constant) bounds the answer length; questions are bounded by the verifier's polynomial; reason: same classes
--   - encoding: NEXP → certificate form: a closed decider halting within $2^{P(|z|)}$ steps on $(z,w)$ for all $|w|\le 2^{Q(|z|)}$, and $z\in L$ iff some such $w$ is accepted; reason: the standard verifier characterization of nondeterministic exponential time
--   - reading: MIP in “NEXP = MIP” → the general classical class of [BFL91]: polynomially many deterministic provers, polynomially many rounds, a randomized polynomial-time verifier on the MIPRE cost model, fixed constants $s<c$; reason: the source distinguishes MIP from the two-prover one-round classes (“MIP[poly, O(1)] = MIP[poly, poly] = NEXP = MIP”, p.70)
--   - encoding: equalities and inclusions of complexity classes → `∀ L, _ ↔ _` (resp. `∀ L, _ → _`) on languages $L\subseteq\{0,1\}^*$; reason: same statements
--   - encoding: $\rho_{\max}$ as a maximum (Definition 2.20) → `sSup` of the set of admissible values $|\mathrm{Tr}[\psi(X\otimes Y^\dagger)]|$; reason: the set is nonempty and bounded and the maximum is attained by compactness, so the supremum equals it
--   - encoding: entries computable in polynomial time: a rational approximation within $2^{-b}$ in time poly$(b)$ → a closed program of the MIPRE cost model computing, on $(b,(i,j))$, codes of two rationals within $2^{-b}$ of $\mathrm{Re}\,\psi_{ij}$ and $\mathrm{Im}\,\psi_{ij}$ within $P(b)$ steps; indices through a fixed enumeration of the index type; reason: the standing assumption of §1.1 on the platform's machine model; time polynomial in the value $b$, as printed
--   - encoding: $\psi^{\otimes n}$ → `tensorPow ψ n`: the same operator with Alice's $n$ registers collected first; reason: a permutation of tensor factors; Alice holds the first qubit of every copy, as in the source
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Theorem 1.1, p.4; §1.1, p.4 (standing assumption)

import Mathlib
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
import Definitions.Def_UnitalMIP_HasMaxMixedMarginals
import Definitions.Def_UnitalMIP_rhoMax
import Definitions.Def_UnitalMIP_EntriesPolyTime
import Definitions.Def_UnitalMIP_MIPPsi
import Definitions.Def_UnitalMIP_NEXP
import Definitions.Def_UnitalMIP_MIP

open scoped Matrix

namespace UnitalMIP

/-- **Theorem 1.1** (Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), §1.1, p.4). Let `ψ ∈ M₂ ⊗ M₂` be a fixed two-qubit state with maximally
mixed marginals.
1. If `ψ` is separable or `ρmax(ψ) < 1`, then `MIP^ψ[poly, poly] = NEXP = MIP`.
2. If `ψ` is entangled and `ρmax(ψ) = 1`, then `MIP^ψ[poly, poly] = RE`.

**Formalization Note**
* The §1.1 standing assumption ("assume that its entries are computable in polynomial time",
  p.4) is the hypothesis `EntriesPolyTime ψ`; it is the source's own hypothesis of the theorem.
* `MIP^ψ[poly, poly]` is `MIPPsiPolyPoly ψ` (Definition 2.15 on the published
  `MIPRE.PolyVerifier`, value `ω*_∞` of (17), fixed constants `s < c`); `NEXP` is in certificate
  form; `MIP` is the general classical multi-prover class of [BFL91]; `RE` is the published
  `MIPRE.IsRE`. Each equality of classes is `∀ L, _ ↔ _` on languages `L ⊆ {0,1}*`.
* Separability is the published `QAlgorithms.Entanglement.IsSeparableDensity`. -/
theorem theorem_1_1 (ψ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hψ : QAlgorithms.IsDensityMatrix ψ) (hmm : HasMaxMixedMarginals ψ)
    (hcomp : EntriesPolyTime ψ) :
    ((QAlgorithms.Entanglement.IsSeparableDensity ψ ∨ rhoMax ψ < 1) →
        (∀ L, MIPPsiPolyPoly ψ L ↔ NEXP L) ∧ (∀ L, NEXP L ↔ MIP L)) ∧
      ((IsEntangled ψ ∧ rhoMax ψ = 1) → ∀ L, MIPPsiPolyPoly ψ L ↔ MIPRE.IsRE L) := by sorry

end UnitalMIP
