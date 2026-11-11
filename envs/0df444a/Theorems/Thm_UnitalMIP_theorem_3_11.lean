-- Prove2me | Theorems.Thm_UnitalMIP_theorem_3_11
-- name    : UnitalMIP.theorem_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:41:55.497008+00:00
-- url     : https://prove2.me/theorems/ebcf7281-ce56-48f2-8d81-fc477d7cc8a6
-- title:
--   Theorem 3.11 — $\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]\subseteq\mathrm{RE}$
-- statement:
--   For every fixed finite-dimensional bipartite state $\psi$ whose entries are computable in polynomial time,
--
--   $$
--   \mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]\subseteq\mathrm{RE}.
--   $$
--
--   This is the upper bound of the second branch: values with a fixed resource can be approximated from below by enumeration.
--
--   **Formalization Note** RE is the published `MIPRE.IsRE`.
--
--   Differences from the source:
--   - reading: the §1.1 standing assumption (stated for the two-qubit ψ) and the proof's “computable approximations to the matrix entries of ψ” (p.75) → the hypothesis that the entries of the finite-dimensional $\psi$ are computable in polynomial time (`EntriesPolyTime ψ`); reason: the proof uses computable entries, and the theorem is plausibly false without some computability of $\psi$; the standing assumption is the paper's own form of it
--   - reading: Definition 2.15: a uniform family of one-round protocols with a classical randomized verifier that samples question pairs and evaluates decision predicates in time polynomial in the input bit length (prose) → the published `MIPRE.PolyVerifier`, efficient on every input: closed sampler and decider programs, seed length and question length at most $P(|z|)$, decider time polynomial in the total input length, strings longer than $P(|z|)$ rejected; reason: the source defines the class in prose; this is the published machine model of the same polynomial-time two-prover one-round verifier, and it imposes no condition on the language
--   - reading: a constant completeness–soundness gap → fixed real constants $s<c$, independent of the input, with $z\in L\Rightarrow\omega^*_\infty(G_z,\psi)\ge c$ and $z\notin L\Rightarrow\omega^*_\infty(G_z,\psi)\le s$; reason: the source's proofs use exactly this form (proof of Theorem 3.11, p.75: completeness $c$, soundness $s<c$; §4.5, p.65); input-dependent thresholds would not be a constant gap
--   - encoding: answers of length at most $a(|z|)$ → the decider rejects whenever an answer is longer than $a(|z|)$ bits; reason: a strategy can map every overlong answer to a short one without lowering its value, so the value is that of the game with answers of length at most $a(|z|)$
--   - encoding: $\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]$ and $\mathrm{MIP}^\psi[\mathrm{poly},O(1)]$ → some polynomial (resp. one constant) bounds the answer length; questions are bounded by the verifier's polynomial; reason: same classes
--   - encoding: equalities and inclusions of complexity classes → `∀ L, _ ↔ _` (resp. `∀ L, _ → _`) on languages $L\subseteq\{0,1\}^*$; reason: same statements
--   - encoding: entries computable in polynomial time: a rational approximation within $2^{-b}$ in time poly$(b)$ → a closed program of the MIPRE cost model computing, on $(b,(i,j))$, codes of two rationals within $2^{-b}$ of $\mathrm{Re}\,\psi_{ij}$ and $\mathrm{Im}\,\psi_{ij}$ within $P(b)$ steps; indices through a fixed enumeration of the index type; reason: the standing assumption of §1.1 on the platform's machine model; time polynomial in the value $b$, as printed
--   - encoding: $\psi^{\otimes n}$ → `tensorPow ψ n`: the same operator with Alice's $n$ registers collected first; reason: a permutation of tensor factors; Alice holds the first qubit of every copy, as in the source
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Theorem 3.11, p.31; proof, p.75; §1.1, p.4 (standing assumption)

import Mathlib
import Definitions.Def_MIPRE_Foundations_ClassMIPStarComputable
import Definitions.Def_UnitalMIP_EntriesPolyTime
import Definitions.Def_UnitalMIP_MIPPsi

open scoped Matrix

namespace UnitalMIP

/-- **Theorem 3.11** (RE upper bound; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.31; proved p.75). For every fixed finite-dimensional
bipartite state `ψ`, `MIP^ψ[poly, poly] ⊆ RE`.

**Formalization Note** The §1.1 standing assumption, that the entries of `ψ` are computable in
polynomial time (`EntriesPolyTime ψ`), is a hypothesis, read for the finite-dimensional `ψ` of this
theorem: the proof uses "computable approximations to the matrix entries of ψ" (p.75). -/
theorem theorem_3_11 {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
    (ψ : Matrix (dA × dB) (dA × dB) ℂ) (hψ : QAlgorithms.IsDensityMatrix ψ)
    (hcomp : EntriesPolyTime ψ) :
    ∀ L, MIPPsiPolyPoly ψ L → MIPRE.IsRE L := by sorry

end UnitalMIP
