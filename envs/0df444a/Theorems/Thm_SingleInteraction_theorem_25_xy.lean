-- Prove2me | Theorems.Thm_SingleInteraction_theorem_25_xy
-- name    : SingleInteraction.theorem_25_xy
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:57:51.78331+00:00
-- url     : https://prove2.me/theorems/09f929d7-f15c-4d73-b184-25efc0d119d3
-- title:
--   Theorem 25 [PM17], stated consequence: $\{X\otimes X+Y\otimes Y\}^+$-Hamiltonian is QMA-complete
-- statement:
--   The positive-weight XY Hamiltonian problem is QMA-complete: for inputs $H=\sum_i\alpha_i(X_{u_i}X_{v_i}+Y_{u_i}Y_{v_i})$ on $n$ qubits with polynomially many terms, coefficients $0\le\alpha_i\le\mathrm{poly}(n)$ given with polynomially many bits, and thresholds $a<b$ with $b-a\ge1/\mathrm{poly}(n)$, deciding whether some state has energy at most $a$ or every state has energy at least $b$ is
--
--   1. in QMA, and
--   2. QMA-hard.
--
--   This is the case $\alpha=\beta=1$, $\gamma=0$ of the first clause of Piddock and Montanaro's classification, which the paper restates and does not prove. It is the source problem of the reduction behind Theorem 60.
--
--   Differences from the source:
--   - reading: QMA as in Definition 2 (an adapted form: error $2^{-\Omega(|x|)}$, ancillas $|0\rangle^{\otimes n_0}|1\rangle^{\otimes n_1}$, an unnamed finite universal gate set) and QMA-hardness under polynomial-time reductions → the published `InQMA` and `QMAHard` of `ContinuumCoulombHardness` (uniform polynomial-size circuits over $\{H,T,\mathrm{CNOT}\}$, ancillas $|0\rangle$, completeness $2/3$, soundness $1/3$; polynomial-time many-one reductions computed by Turing machines), applied to bit strings through the instance codec; reason: Remark 1 and the sentence before Definition 2 (p.16) declare Definition 2 an equivalent formulation of the standard class, obtained by standard amplification; the published class adds no condition the paper's notion lacks
--   - reading: "$M=\mathrm{poly}(n)$" terms, coefficients polynomially bounded and with polynomially many bits, thresholds with $\mathrm{poly}(n)$ bits and "$b-a\ge 1/\mathrm{poly}(n)$", one problem that is QMA-complete → one exponent $c$: at most $(n+1)^c$ terms, $0\le\alpha_i\le(n+1)^c$, code lengths of $\alpha_i,a,b$ at most $(n+1)^c$ and $b-a\ge (n+1)^{-c}$; membership in QMA for every $c$, QMA-hardness for some $c$; reason: the polynomial is unspecified; hardness at $c$ gives hardness at every $c'\ge c$ because the valid sets grow, so this is the strongest reading of completeness
--   - encoding: "$V_i$ specifies the qubits on which the interaction is applied", coefficients real with polynomially many bits → terms $(u_i,v_i,\alpha_i)$ with $u_i\ne v_i<n$ and $\alpha_i$ a binary rational; reason: the interaction is two-local and symmetric, so an ordered pair of distinct qubits specifies its support; a coefficient with polynomially many bits is a binary rational
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.3.5, p.26, Theorem 25 [PM17] and the sentence after it

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_XYWeightedInstance
import Definitions.Def_SingleInteraction_xyPlusProblem

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- The positive-weight XY Hamiltonian problem is QMA-complete (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.3.5, p.26, the consequence
of Theorem 25 [PM17] stated there: "In particular, taking `α = β = 1` and `γ = 0` in the first case shows
that `{X ⊗ X + Y ⊗ Y}⁺`-Hamiltonian is QMA-complete").

**Formalization Note** The QMA notions are the published \`OAI.ContinuumCoulomb.InQMA\` (uniform polynomial-size {H, T, CNOT} verifiers, ancillas \`|0⟩\`, completeness 2/3, soundness 1/3) and \`QMAHard\` (polynomial-time many-one reductions from every QMA bit-string promise problem), applied to the instance problem through its codec; the paper's Definition 2 (p.16) is an equivalent formulation by its Remark 1. "\`poly(n)\`" is the exponent \`c\`: membership is stated for every \`c\`, hardness for some \`c\`. The result is cited from Piddock–Montanaro; this paper does not prove
it. -/
theorem theorem_25_xy :
    (∀ c : ℕ, InQMA (onCodes xyWeightedCodec (xyPlusProblem c))) ∧
      ∃ c : ℕ, QMAHard xyWeightedCodec.encode (xyPlusProblem c) := by sorry

end SingleInteraction
