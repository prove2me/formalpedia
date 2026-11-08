-- Prove2me | Theorems.Thm_SingleInteraction_lemma_42
-- name    : SingleInteraction.lemma_42
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:19.427025+00:00
-- url     : https://prove2.me/theorems/1caef4f0-8c03-45c0-a0f9-248a832f895f
-- title:
--   Lemma 42 — $\mathrm{SIH}_k,\mathrm{DSIH}_k\in\mathrm{QMA}$
-- statement:
--   For constant $k$:
--
--   1. for every Hermitian $k$-qubit interaction $h$ with polynomial-time computable entries, $\mathrm{SIH}_k$ with interaction $h$ is in QMA;
--   2. for every uniform family $\{h^{(n)}\}_{n\ge1}$ of Hermitian $k$-qubit interactions with $\|h^{(n)}\|\le\mathrm{poly}(n)$, $\mathrm{DSIH}_k$ is in QMA.
--
--   Each holds for every polynomial bound on the input's precision and gap. Membership in Theorem 60 is the case $k=2$ of the first clause.
--
--   Differences from the source:
--   - reading: QMA as in Definition 2 (an adapted form: error $2^{-\Omega(|x|)}$, ancillas $|0\rangle^{\otimes n_0}|1\rangle^{\otimes n_1}$, an unnamed finite universal gate set) and QMA-hardness under polynomial-time reductions → the published `InQMA` and `QMAHard` of `ContinuumCoulombHardness` (uniform polynomial-size circuits over $\{H,T,\mathrm{CNOT}\}$, ancillas $|0\rangle$, completeness $2/3$, soundness $1/3$; polynomial-time many-one reductions computed by Turing machines), applied to bit strings through the instance codec; reason: Remark 1 and the sentence before Definition 2 (p.16) declare Definition 2 an equivalent formulation of the standard class, obtained by standard amplification; the published class adds no condition the paper's notion lacks
--   - reading: thresholds with $\mathrm{poly}(n)$ bits and "$b-a\ge 1/\mathrm{poly}(n)$" → one exponent $c$ with code lengths $\le (n+1)^c$ and $b-a\ge (n+1)^{-c}$; membership in QMA for every $c$; reason: the polynomial is unspecified; membership for every $c$ covers every polynomial
--   - encoding: input: $n$ in unary, a set $L$ of $M=\mathrm{poly}(n)$ ordered tuples, two real thresholds with polynomially many bits → a structure with $n$, a duplicate-free list of tuples (each a list of qubit indices) and two binary rationals with positive denominators, coded by the published combinators; no separate bound on $M$; reason: the same inputs; a duplicate-free list of ordered tuples is a set of them; pairwise distinct ordered tuples of distinct qubits number at most $n^k$, so the bound on $M$ is automatic for constant $k$
--   - encoding: rational approximations to the entries with additive error $2^{-q}$ in time polynomial in $q$ (and $n$); $\|h^{(n)}\|\le\mathrm{poly}(n)$ → a polynomial-time Turing machine on (unary $q$, unary $n$, entry index) returning a Gaussian rational within modulus $2^{-q}$; $\|h^{(n)}\|\le Cn^d$ for $n\ge1$; reason: the entry index is part of the algorithm's input; for constant $k$ it adds $O(k)$ symbols
--   - reading: "For constant $k$", with $h$ Hermitian and computable as required by Definitions 31 and 32 → $\forall k\in\mathbb N$ quantified before the problem ($k=0$ is not excluded by the source and is a scalar case), with the Hermitian and computability requirements as hypotheses of the theorem rather than of the promise problem; reason: $k$ is fixed before the instance; the requirements restrict the interaction, not the instances
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §3.4, p.33, Lemma 42

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_SIHInstance
import Definitions.Def_SingleInteraction_sihProblem
import Definitions.Def_SingleInteraction_dsihProblem
import Definitions.Def_SingleInteraction_EntriesPolyTime
import Definitions.Def_SingleInteraction_UniformFamily

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- Lemma 42 (Containment of Unpinned Variants) (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §3.4, p.33): "For constant `k`,
`SIHk, DSIHk ∈ QMA`."

1. For every `k` and every Hermitian `k`-qubit `h` with polynomial-time computable entries (Definition 31),
   `SIH_k` is in QMA, for every polynomial exponent `c`;
2. for every `k` and every family `{h^(n)}_{n≥1}` of Hermitian `k`-qubit matrices that is uniformly computable
   with `‖h^(n)‖ ≤ poly(n)` (Definition 32), `DSIH_k` is in QMA, for every `c`.

**Formalization Note** The QMA notions are the published \`OAI.ContinuumCoulomb.InQMA\` (uniform polynomial-size {H, T, CNOT} verifiers, ancillas \`|0⟩\`, completeness 2/3, soundness 1/3), applied to the instance problem through its codec; the paper's Definition 2 (p.16) is an equivalent formulation by its Remark 1. "\`poly(n)\`" is the exponent \`c\`: membership is stated for every \`c\`. "For constant `k`" is `k` quantified before the problem. The Hermitian and computability requirements of Definitions 31 and 32 are hypotheses. -/
theorem lemma_42 :
    (∀ (k : ℕ) (h : Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ), h.IsHermitian → EntriesPolyTime h →
        ∀ c : ℕ, InQMA (onCodes sihCodec (sihProblem k h c))) ∧
      ∀ (k : ℕ) (hfam : ℕ → Matrix (Fin k → Fin 2) (Fin k → Fin 2) ℂ),
        (∀ n : ℕ, 1 ≤ n → (hfam n).IsHermitian) → UniformFamily hfam →
          ∀ c : ℕ, InQMA (onCodes sihCodec (dsihProblem k hfam c)) := by sorry

end SingleInteraction
