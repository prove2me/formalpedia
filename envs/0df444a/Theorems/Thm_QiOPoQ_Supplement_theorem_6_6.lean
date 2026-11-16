-- Prove2me | Theorems.Thm_QiOPoQ_Supplement_theorem_6_6
-- name    : QiOPoQ.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:15:54.389696+00:00
-- url     : https://prove2.me/theorems/4833d2fe-17df-47de-a386-dc692b7797ec
-- title:
--   Theorem 6.6: Assumptions 6.2, 6.3, 6.5 give qiO for polynomial-size ancilla-free unitary families of width at least λ
-- statement:
--   Under Assumptions 6.2, 6.3 and 6.5, there is a quantum iO scheme for polynomial-size ancilla-free unitary circuit families of width at least $\lambda$.
--
--   Precisely: if there are $p_1,p_2$, classical PPT transformations RIO, Encode and functions $s,N$ such that Assumption 6.2 holds for $p_1,p_2$, Assumption 6.3 holds for $p_1,p_2,\mathrm{RIO},\mathrm{Encode},s,N$, and Assumption 6.5 holds for the reference distributions of Definition 6.4 built from $\mathrm{RIO},\mathrm{Encode},s,N$, then there is a classical PPT obfuscator that is correct (Definition 3.1) and qiO-secure against non-uniform QPT adversaries (Definition 3.2) for the class of polynomial-size ancilla-free unitary circuit families of width at least $\lambda$.
--
--   This is the local-mixing route to quantum iO; with Theorem 6.7 and Corollary 6.8 it yields the qiO that Sections 4 and 5 assume.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any gate set with designated I, X, CNOT and an adjoint map (QiOPoQ.GateSet); reason: the statement for every such gate set specializes to the paper's fixed one; the adversary model is taken over the same gate set
--   - reading: Under Assumptions 6.2, 6.3 and 6.5 → one existential over the shared data (p1, p2, RIO, Encode, s, N) with Assumption62 ∧ Assumption63 ∧ Assumption65; reason: Assumption 6.3 refers to the p1, p2 of Assumption 6.2, and Assumption 6.5 to Definition 6.4, built from RIO, Encode, s, N
--   - reading: nonnegative polynomial-time computable functions p1, p2; length conditions 'whenever …' → ℕ-valued p1, p2 computed on unary codes; the conditions required at every λ; reason: a polynomial-time computable function outputs a number given by a string, read as a natural number (p1 multiplies gate counts, p2 bounds a gate count); requiring the conditions at every λ is the weaker hypothesis
--   - reading: N(λ, n, k) ≥ k → for the three lengths k ∈ {s, 2s, 2s + 1}; reason: the lengths at which Assumption 6.3 is stated and used; the weaker hypothesis
--   - reading: every joint distribution (aux, C) of polynomial-size classical descriptions with C marginally uniform over C_{n,k} → C ← C_{n,k} with an arbitrary conditional law (PMF) of aux given C on strings of polynomially bounded length; reason: every such joint distribution has this form; not restricted to samplable ones
--   - reading: RIO, Encode: transformations of ancilla-free circuits with Definition 3.1's correctness → outputs read as ancilla-free circuits of the same width n (IsAFCorrect); reason: Definition 6.4 and the construction concatenate them
--   - encoding: §6 ancilla-free n-qubit circuits, C_{n,N}, E_{C,N} → gate lists on n wires with all wires as output in order (afCirc); uniform placements; uniform over equal channels; a distribution on an empty set has value 0; reason: used only where defined (N ≥ |C|)
--   - encoding: Definition 6.4's output RIO(L)∥Encode(D_1)∥⋯∥RIO(R†) → the description of the concatenation of the decoded output circuits (empty string if a piece is not such a circuit); reason: fixed reading of ∥ on outputs
--   - reading: polynomial-size ancilla-free unitary circuit families of width at least λ → IsAFUnitaryWide: PolySize ∧ n_anc = 0 ∧ unitary (§3.1, any order of the output wires) ∧ n_in + n_anc ≥ λ; reason: the §3.1 classes C_unitary and C^{anc-free}
--   - reading: non-uniform QPT algorithms (adversaries, provers, distinguishers, inverters) → NUQPT: classical advice of polynomial length, coins, a classical polynomial-time generator of circuits over the gate set run on |0…0⟩ and measured, and classical polynomial-time post-processing; reason: the paper never uses quantum advice and excludes quantum auxiliary inputs (§3.1); over a universal gate set adaptivity and intermediate measurements can be deferred into the circuits
--   - encoding: PPT algorithms and classical polynomial-time algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count (and advice for non-uniform ones), on fixed self-delimiting encodings; reason: the standard model; same instances as the base mission
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 6.6, p.32; Assumptions 6.2, 6.3, 6.5 and Definition 6.4, pp.31–32; Notation 6.1, p.30

import Mathlib
import Definitions.Def_QiOPoQ_Supplement_IsObfCorrectOn
import Definitions.Def_QiOPoQ_Supplement_IsQiOQuantumOn
import Definitions.Def_QiOPoQ_Supplement_IsAFUnitaryWide
import Definitions.Def_QiOPoQ_Supplement_Assumption62
import Definitions.Def_QiOPoQ_Supplement_Assumption63
import Definitions.Def_QiOPoQ_Supplement_Assumption65

set_option autoImplicit false

open QAlgorithms.Complexity

namespace QiOPoQ.Supplement

/-- **Theorem 6.6 (qiO for ancilla-free unitary circuits).** Gheorghiu, Gupte, Havlíček, Liu,
*Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289
(sha256 fe2f9210…), Theorem 6.6, p.32: "Under Assumptions 6.2, 6.3 and 6.5, there is a quantum iO
scheme for polynomial-size ancilla-free unitary circuit families of width at least λ."

If there are `p1, p2` (Assumption 6.2) and `RIO, Encode, s, N` (Assumption 6.3) such that
Assumptions 6.2, 6.3 and 6.5 hold for these data, then there is a classical PPT obfuscator that is
correct (Definition 3.1) and qiO-secure against non-uniform QPT adversaries (Definition 3.2) for
the class of polynomial-size ancilla-free unitary circuit families of width at least `λ`.

**Formalization Note.** The three assumptions share their data (Assumption 6.3 refers to the
`p1, p2` of Assumption 6.2, and Assumption 6.5 to the reference distribution of Definition 6.4,
built from `RIO, Encode, s, N`), so the hypothesis is one existential over all of it. The
obfuscator is classical (Definition 3.1, footnote 11). -/
theorem theorem_6_6 (G : GateSet)
    (hA : ∃ (p1 p2 : ℕ → ℕ → ℕ) (RIO Enc : UPPT) (s : ℕ → ℕ → ℕ) (N : ℕ → ℕ → ℕ → ℕ),
      Assumption62 G p1 p2 ∧ Assumption63 G p1 p2 RIO Enc s N ∧ Assumption65 G RIO Enc s N) :
    ∃ Obf : UPPT, IsObfCorrectOn G IsAFUnitaryWide Obf ∧ IsQiOQuantumOn G IsAFUnitaryWide Obf := by sorry

end QiOPoQ.Supplement
