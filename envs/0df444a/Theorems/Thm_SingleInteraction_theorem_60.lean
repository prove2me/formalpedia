-- Prove2me | Theorems.Thm_SingleInteraction_theorem_60
-- name    : SingleInteraction.theorem_60
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:35.724396+00:00
-- url     : https://prove2.me/theorems/72c3f65e-b9c9-4998-b805-0c4965080396
-- title:
--   Theorem 60 — $\mathrm{SIH}_2$ with $h=Z\otimes Z+X\otimes Y-Y\otimes X$ is QMA-complete
-- statement:
--   Let $h=Z\otimes Z+X\otimes Y-Y\otimes X$. Then $h$ is a Hermitian two-qubit interaction with polynomial-time computable entries, and the problem $\mathrm{SIH}_2$ for $h$ is QMA-complete:
--
--   1. given $n$, a set $L$ of pairwise distinct ordered pairs $(u,v)$ of distinct qubits among $n$, and thresholds $a,b$ with polynomially many bits and $b-a\ge1/\mathrm{poly}(n)$, let
--
--   $$H=\sum_{(u,v)\in L}h_{u,v};$$
--
--   2. deciding whether some $n$-qubit state has $\langle\phi|H|\phi\rangle\le a$ or every $n$-qubit state has $\langle\phi|H|\phi\rangle\ge b$ is in QMA and QMA-hard.
--
--   In particular there is a fixed two-local Hermitian interaction whose single-interaction problem is QMA-complete: every local term is an unweighted copy of the same $h$, so the hardness is carried by the interaction graph and the orientation of its edges.
--
--   Differences from the source:
--   - reading: QMA as in Definition 2 (an adapted form: error $2^{-\Omega(|x|)}$, ancillas $|0\rangle^{\otimes n_0}|1\rangle^{\otimes n_1}$, an unnamed finite universal gate set) and QMA-hardness under polynomial-time reductions → the published `InQMA` and `QMAHard` of `ContinuumCoulombHardness` (uniform polynomial-size circuits over $\{H,T,\mathrm{CNOT}\}$, ancillas $|0\rangle$, completeness $2/3$, soundness $1/3$; polynomial-time many-one reductions computed by Turing machines), applied to bit strings through the instance codec; reason: Remark 1 and the sentence before Definition 2 (p.16) declare Definition 2 an equivalent formulation of the standard class, obtained by standard amplification; the published class adds no condition the paper's notion lacks
--   - reading: "$\mathrm{poly}(n)$" bits for the thresholds and "$b-a\ge 1/\mathrm{poly}(n)$", one problem that is QMA-complete → one exponent $c$ with code lengths $\le (n+1)^c$ and $b-a\ge (n+1)^{-c}$; membership in QMA for every $c$, QMA-hardness for some $c$; reason: the polynomial is unspecified; hardness at $c$ gives hardness at every $c'\ge c$ because the valid sets grow, so this is the strongest reading of completeness
--   - encoding: input: $n$ in unary, a set $L$ of $M=\mathrm{poly}(n)$ ordered tuples, two real thresholds with polynomially many bits → a structure with $n$, a duplicate-free list of tuples (each a list of qubit indices) and two binary rationals with positive denominators, coded by the published combinators; no separate bound on $M$; reason: the same inputs; a duplicate-free list of ordered tuples is a set of them; pairwise distinct ordered pairs of distinct qubits number at most $n(n-1)$, so the bound on $M$ is automatic
--   - reading: "There exists a fixed 2-local Hermitian interaction $h$ … In particular, one may take" $h$ of (30) → the statement about the explicit $h$ of (30), with no existential; reason: the second sentence implies the first
--   - encoding: "We require the entries of $h$ to be polynomial-time computable" (Definition 31): rational approximations with additive error $2^{-q}$ in time polynomial in $q$ → the conjunct `EntriesPolyTime hSIH`: a polynomial-time Turing machine on (unary $q$, entry index) returning a Gaussian rational within modulus $2^{-q}$; reason: Definition 31 requires this of the interaction of the problem; the entry index is part of the algorithm's input and adds $O(1)$ symbols for $k=2$
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1, p.55, Theorem 60 and eq. (30)

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_hSIH
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_SIHInstance
import Definitions.Def_SingleInteraction_sihProblem
import Definitions.Def_SingleInteraction_EntriesPolyTime

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- Theorem 60 (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1, p.55): "There exists a fixed 2-local Hermitian interaction `h` such that the
corresponding `SIH2` problem is QMA-complete. In particular, one may take `h = Z ⊗ Z + X ⊗ Y − Y ⊗ X`. (30)"

For `h = Z⊗Z + X⊗Y − Y⊗X`: `h` is Hermitian, its entries are polynomial-time computable (Definition 31),
`SIH_2` with interaction `h` (unweighted copies of `h` on pairwise distinct ordered pairs of distinct
qubits) is in QMA for every polynomial exponent `c`, and it is QMA-hard for some `c`.

**Formalization Note** The QMA notions are the published \`OAI.ContinuumCoulomb.InQMA\` (uniform polynomial-size {H, T, CNOT} verifiers, ancillas \`|0⟩\`, completeness 2/3, soundness 1/3) and \`QMAHard\` (polynomial-time many-one reductions from every QMA bit-string promise problem), applied to the instance problem through its codec; the paper's Definition 2 (p.16) is an equivalent formulation by its Remark 1. "\`poly(n)\`" is the exponent \`c\`: membership is stated for every \`c\`, hardness for some \`c\`. Naming the explicit `h` states the theorem's second sentence, which
implies the first. -/
theorem theorem_60 :
    hSIH.IsHermitian ∧ EntriesPolyTime hSIH ∧
      (∀ c : ℕ, InQMA (onCodes sihCodec (sihProblem 2 hSIH c))) ∧
        ∃ c : ℕ, QMAHard sihCodec.encode (sihProblem 2 hSIH c) := by sorry

end SingleInteraction
