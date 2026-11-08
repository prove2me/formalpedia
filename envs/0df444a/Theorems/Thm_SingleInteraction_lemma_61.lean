-- Prove2me | Theorems.Thm_SingleInteraction_lemma_61
-- name    : SingleInteraction.lemma_61
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:01.361198+00:00
-- url     : https://prove2.me/theorems/67891dac-1ae8-4fd5-93c0-6cf87662e73f
-- title:
--   Lemma 61 — positive-integer-weight and occurrence-list XY Hamiltonians are QMA-complete
-- statement:
--   The restriction of the positive-weight XY problem to positive integer coupling strengths of polynomial magnitude, $H=\sum_iw_iK_{u_iv_i}$ with $w_i\in\{1,\dots,\mathrm{poly}(n)\}$, is QMA-complete. Equivalently, the Hamiltonian may be given as a polynomial-length list of occurrences
--
--   $$K=\sum_{e=1}^MK_{u_ev_e},\qquad K_{uv}=X_uX_v+Y_uY_v,$$
--
--   with repeated occurrences on the same pair allowed; this occurrence-list problem is QMA-complete as well. Both forms are stated: each problem is in QMA and QMA-hard.
--
--   The occurrence list is the form consumed by the gadget of §5.1.2, which realizes each occurrence with fresh mediator qubits.
--
--   Differences from the source:
--   - reading: QMA as in Definition 2 (an adapted form: error $2^{-\Omega(|x|)}$, ancillas $|0\rangle^{\otimes n_0}|1\rangle^{\otimes n_1}$, an unnamed finite universal gate set) and QMA-hardness under polynomial-time reductions → the published `InQMA` and `QMAHard` of `ContinuumCoulombHardness` (uniform polynomial-size circuits over $\{H,T,\mathrm{CNOT}\}$, ancillas $|0\rangle$, completeness $2/3$, soundness $1/3$; polynomial-time many-one reductions computed by Turing machines), applied to bit strings through the instance codec; reason: Remark 1 and the sentence before Definition 2 (p.16) declare Definition 2 an equivalent formulation of the standard class, obtained by standard amplification; the published class adds no condition the paper's notion lacks
--   - reading: "positive integer coupling strengths of polynomial magnitude", "a polynomial-length list", thresholds with $\mathrm{poly}(n)$ bits and "$b-a\ge 1/\mathrm{poly}(n)$", one problem that is QMA-complete → one exponent $c$: integer weights $1\le w_i\le(n+1)^c$, at most $(n+1)^c$ terms or occurrences, threshold codes of at most $(n+1)^c$ bits and $b-a\ge (n+1)^{-c}$; membership in QMA for every $c$, QMA-hardness for some $c$; reason: the polynomial is unspecified; hardness at $c$ gives hardness at every $c'\ge c$ because the valid sets grow, so this is the strongest reading of completeness
--   - reading: the integer-weight problem is QMA-complete; "Equivalently" it may be specified as an occurrence list → both problems stated, each in QMA for every $c$ and QMA-hard for some $c$; reason: the two conjuncts together imply either form; the equivalence of the encodings is not itself asserted as a separate formula
--   - encoding: terms and occurrences on qubit pairs, integer weights → terms $(u,v,w)$ and occurrences $(u,v)$ with $u\ne v<n$, $w$ a natural number in binary, as lists; thresholds binary rationals with positive denominators; reason: the interaction is two-local and symmetric, every occurrence acts on two distinct work qubits (p.57), and repeated occurrences are lists with repeats
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §5.1.1, p.55, Lemma 61

import Mathlib
import Definitions.Def_ContinuumCoulombHardness
import Definitions.Def_SingleInteraction_onCodes
import Definitions.Def_SingleInteraction_XYIntInstance
import Definitions.Def_SingleInteraction_xyIntProblem
import Definitions.Def_SingleInteraction_XYOccInstance
import Definitions.Def_SingleInteraction_xyOccProblem

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- Lemma 61 (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), p.55): "The restriction of `{X ⊗ X + Y ⊗ Y}⁺`-Hamiltonian to positive integer
coupling strengths of polynomial magnitude is QMA-complete. Equivalently, the Hamiltonian may be specified
as a polynomial-length list of interaction occurrences, `K = Σ_{e=1}^M K_{u_e v_e}`, where repeated
occurrences on the same qubit pair are permitted."

Both forms are stated: the positive-integer-weight problem (`xyIntProblem`) and the occurrence-list
problem (`xyOccProblem`) are each in QMA for every polynomial exponent and QMA-hard for some.

**Formalization Note** The QMA notions are the published \`OAI.ContinuumCoulomb.InQMA\` (uniform polynomial-size {H, T, CNOT} verifiers, ancillas \`|0⟩\`, completeness 2/3, soundness 1/3) and \`QMAHard\` (polynomial-time many-one reductions from every QMA bit-string promise problem), applied to the instance problem through its codec; the paper's Definition 2 (p.16) is an equivalent formulation by its Remark 1. "\`poly(n)\`" is the exponent \`c\`: membership is stated for every \`c\`, hardness for some \`c\`. -/
theorem lemma_61 :
    ((∀ c : ℕ, InQMA (onCodes xyIntCodec (xyIntProblem c))) ∧
        ∃ c : ℕ, QMAHard xyIntCodec.encode (xyIntProblem c)) ∧
      ((∀ c : ℕ, InQMA (onCodes xyOccCodec (xyOccProblem c))) ∧
        ∃ c : ℕ, QMAHard xyOccCodec.encode (xyOccProblem c)) := by sorry

end SingleInteraction
