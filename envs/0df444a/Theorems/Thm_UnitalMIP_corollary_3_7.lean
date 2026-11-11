-- Prove2me | Theorems.Thm_UnitalMIP_corollary_3_7
-- name    : UnitalMIP.corollary_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:41:24.046601+00:00
-- url     : https://prove2.me/theorems/a19197ed-cef3-48d7-b34f-400fa2a96010
-- title:
--   Corollary 3.7 — $\mathrm{MIP}^\psi[\mathrm{poly},O(1)]=\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]=\mathrm{NEXP}=\mathrm{MIP}$ when $\rho_{\max}(\psi)<1$
-- statement:
--   Fix a two-qubit state $\psi$ with maximally mixed marginals and $\rho_{\max}(\psi)<1$, whose entries are computable in polynomial time. Then
--
--   $$
--   \mathrm{MIP}^\psi[\mathrm{poly},O(1)]=\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]=\mathrm{NEXP}=\mathrm{MIP}.
--   $$
--
--   It combines Theorem 3.6 with the noisy-MES lower bound of Dong et al. and the classical MIP = NEXP.
--
--   **Formalization Note** The computability hypothesis is the §1.1 standing assumption (the corollary rests on Theorem 3.6).
--
--   Differences from the source:
--   - reading: Definition 2.15: a uniform family of one-round protocols with a classical randomized verifier that samples question pairs and evaluates decision predicates in time polynomial in the input bit length (prose) → the published `MIPRE.PolyVerifier`, efficient on every input: closed sampler and decider programs, seed length and question length at most $P(|z|)$, decider time polynomial in the total input length, strings longer than $P(|z|)$ rejected; reason: the source defines the class in prose; this is the published machine model of the same polynomial-time two-prover one-round verifier, and it imposes no condition on the language
--   - reading: a constant completeness–soundness gap → fixed real constants $s<c$, independent of the input, with $z\in L\Rightarrow\omega^*_\infty(G_z,\psi)\ge c$ and $z\notin L\Rightarrow\omega^*_\infty(G_z,\psi)\le s$; reason: the source's proofs use exactly this form (proof of Theorem 3.11, p.75: completeness $c$, soundness $s<c$; §4.5, p.65); input-dependent thresholds would not be a constant gap
--   - encoding: answers of length at most $a(|z|)$ → the decider rejects whenever an answer is longer than $a(|z|)$ bits; reason: a strategy can map every overlong answer to a short one without lowering its value, so the value is that of the game with answers of length at most $a(|z|)$
--   - encoding: $\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]$ and $\mathrm{MIP}^\psi[\mathrm{poly},O(1)]$ → some polynomial (resp. one constant) bounds the answer length; questions are bounded by the verifier's polynomial; reason: same classes
--   - encoding: NEXP → certificate form: a closed decider halting within $2^{P(|z|)}$ steps on $(z,w)$ for all $|w|\le 2^{Q(|z|)}$, and $z\in L$ iff some such $w$ is accepted; reason: the standard verifier characterization of nondeterministic exponential time
--   - reading: MIP in “NEXP = MIP” → the general classical class of [BFL91]: polynomially many deterministic provers, polynomially many rounds, a randomized polynomial-time verifier on the MIPRE cost model, fixed constants $s<c$; reason: the source distinguishes MIP from the two-prover one-round classes (“MIP[poly, O(1)] = MIP[poly, poly] = NEXP = MIP”, p.70)
--   - encoding: equalities and inclusions of complexity classes → `∀ L, _ ↔ _` (resp. `∀ L, _ → _`) on languages $L\subseteq\{0,1\}^*$; reason: same statements
--   - encoding: entries computable in polynomial time: a rational approximation within $2^{-b}$ in time poly$(b)$ → a closed program of the MIPRE cost model computing, on $(b,(i,j))$, codes of two rationals within $2^{-b}$ of $\mathrm{Re}\,\psi_{ij}$ and $\mathrm{Im}\,\psi_{ij}$ within $P(b)$ steps; indices through a fixed enumeration of the index type; reason: the standing assumption of §1.1 on the platform's machine model; time polynomial in the value $b$, as printed
--   - encoding: $\psi^{\otimes n}$ → `tensorPow ψ n`: the same operator with Alice's $n$ registers collected first; reason: a permutation of tensor factors; Alice holds the first qubit of every copy, as in the source
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Corollary 3.7, p.30; §1.1, p.4 (standing assumption)

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

/-- **Corollary 3.7** (NEXP characterization; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.30). Fix a two-qubit state `ψ` with maximally
mixed marginals and `ρmax(ψ) < 1`. Then `MIP^ψ[poly, O(1)] = MIP^ψ[poly, poly] = NEXP = MIP`.

**Formalization Note** The §1.1 standing assumption `EntriesPolyTime ψ` is a hypothesis (the
corollary rests on Theorem 3.6). Each equality of classes is `∀ L, _ ↔ _`; `MIP` is the general
classical multi-prover class. -/
theorem corollary_3_7 (ψ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hψ : QAlgorithms.IsDensityMatrix ψ) (hmm : HasMaxMixedMarginals ψ) (hρ : rhoMax ψ < 1)
    (hcomp : EntriesPolyTime ψ) :
    ∀ L, (MIPPsiPolyConst ψ L ↔ MIPPsiPolyPoly ψ L) ∧ (MIPPsiPolyPoly ψ L ↔ NEXP L) ∧
      (NEXP L ↔ MIP L) := by sorry

end UnitalMIP
