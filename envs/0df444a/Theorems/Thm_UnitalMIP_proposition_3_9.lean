-- Prove2me | Theorems.Thm_UnitalMIP_proposition_3_9
-- name    : UnitalMIP.proposition_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:41:19.225564+00:00
-- url     : https://prove2.me/theorems/6ad3f03e-ab9e-4dd5-bbb6-8dea67ab14b2
-- title:
--   Proposition 3.9 — separable resources are classical
-- statement:
--   Let $\psi$ be a fixed finite-dimensional separable bipartite state. For every nonlocal game $G$, optimization over arbitrary finite tensor powers of $\psi$ has exactly the classical value: $\omega^*_n(G,\psi)$ equals the classical value of $G$ for every $n\ge1$. Consequently,
--
--   $$
--   \mathrm{MIP}^\psi[\mathrm{poly},O(1)]=\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]=\mathrm{NEXP}.
--   $$
--
--   This settles the separable case of the first branch, including $\rho_{\max}(\psi)=1$.
--
--   **Formalization Note** Separability is the published `IsSeparableDensity` (a finite convex combination of product density matrices), which needs nonempty index types; these are implied by $\psi$ being a state. No computability of $\psi$ is assumed: the statement and its proof do not use it.
--
--   Differences from the source:
--   - reading: “optimization over arbitrary finite tensor powers of ψ has exactly the classical value” → $\omega^*_n(G,\psi)=$ classical value of $G$ for every $n\ge1$; reason: the proof's “for each finite n”; it implies the same for $\omega^*_\infty$
--   - reading: Definition 2.15: a uniform family of one-round protocols with a classical randomized verifier that samples question pairs and evaluates decision predicates in time polynomial in the input bit length (prose) → the published `MIPRE.PolyVerifier`, efficient on every input: closed sampler and decider programs, seed length and question length at most $P(|z|)$, decider time polynomial in the total input length, strings longer than $P(|z|)$ rejected; reason: the source defines the class in prose; this is the published machine model of the same polynomial-time two-prover one-round verifier, and it imposes no condition on the language
--   - reading: a constant completeness–soundness gap → fixed real constants $s<c$, independent of the input, with $z\in L\Rightarrow\omega^*_\infty(G_z,\psi)\ge c$ and $z\notin L\Rightarrow\omega^*_\infty(G_z,\psi)\le s$; reason: the source's proofs use exactly this form (proof of Theorem 3.11, p.75: completeness $c$, soundness $s<c$; §4.5, p.65); input-dependent thresholds would not be a constant gap
--   - encoding: answers of length at most $a(|z|)$ → the decider rejects whenever an answer is longer than $a(|z|)$ bits; reason: a strategy can map every overlong answer to a short one without lowering its value, so the value is that of the game with answers of length at most $a(|z|)$
--   - encoding: $\mathrm{MIP}^\psi[\mathrm{poly},\mathrm{poly}]$ and $\mathrm{MIP}^\psi[\mathrm{poly},O(1)]$ → some polynomial (resp. one constant) bounds the answer length; questions are bounded by the verifier's polynomial; reason: same classes
--   - encoding: NEXP → certificate form: a closed decider halting within $2^{P(|z|)}$ steps on $(z,w)$ for all $|w|\le 2^{Q(|z|)}$, and $z\in L$ iff some such $w$ is accepted; reason: the standard verifier characterization of nondeterministic exponential time
--   - encoding: equalities and inclusions of complexity classes → `∀ L, _ ↔ _` (resp. `∀ L, _ → _`) on languages $L\subseteq\{0,1\}^*$; reason: same statements
--   - encoding: $\psi^{\otimes n}$ → `tensorPow ψ n`: the same operator with Alice's $n$ registers collected first; reason: a permutation of tensor factors; Alice holds the first qubit of every copy, as in the source
--   - generalization: the §1.1 standing assumption (“Throughout, let ψ be a fixed two-qubit state … and assume that its entries are computable in polynomial time”, p.4), read for the finite-dimensional ψ as in Theorem 3.11 → any finite-dimensional separable density matrix ψ, with no computability hypothesis; reason: the fixed-resource value equals the classical value, which does not depend on ψ, so neither inclusion needs the entries of ψ (the proof, p.70, does not use them); it specializes to the source's claim on every computable ψ
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), Proposition 3.9, p.31; proof, p.70

import Mathlib
import Definitions.Def_UnitalMIP_omegaInf
import Definitions.Def_UnitalMIP_MIPPsi
import Definitions.Def_UnitalMIP_NEXP

open scoped Matrix

namespace UnitalMIP

/-- **Proposition 3.9** (Separable resources are classical; Dong, Jiang, Qin, Yao, Zhou, *A Dichotomy for MIP* in the Presence of Unital Noise*, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), p.31; proved p.70). Let `ψ` be a
fixed finite-dimensional separable bipartite state. For every nonlocal game `G`, optimization over
arbitrary finite tensor powers of `ψ` has exactly the classical value. Consequently
`MIP^ψ[poly, O(1)] = MIP^ψ[poly, poly] = NEXP`.

**Formalization Note** "Optimization over arbitrary finite tensor powers has exactly the classical
value" is stated for each number of copies, `ω*_n(G, ψ) = classical value of G` for every `n ≥ 1`
(the proof's "for each finite n"); it implies the same for `ω*_∞`. Separability is the published
`QAlgorithms.Entanglement.IsSeparableDensity` (which includes being a density matrix). No
computability of `ψ` is assumed: the source's statement and proof do not use it. -/
theorem proposition_3_9 {dA dB : Type} [Fintype dA] [DecidableEq dA] [Nonempty dA]
    [Fintype dB] [DecidableEq dB] [Nonempty dB]
    (ψ : Matrix (dA × dB) (dA × dB) ℂ) (hsep : QAlgorithms.Entanglement.IsSeparableDensity ψ) :
    (∀ (X Y A B : Type) [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
        (G : MIPRE.Game X Y A B) (n : ℕ), 1 ≤ n → omegaN G ψ n = classicalValue G) ∧
      ∀ L, (MIPPsiPolyConst ψ L ↔ MIPPsiPolyPoly ψ L) ∧ (MIPPsiPolyPoly ψ L ↔ NEXP L) := by sorry

end UnitalMIP
