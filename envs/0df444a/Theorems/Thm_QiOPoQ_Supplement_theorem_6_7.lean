-- Prove2me | Theorems.Thm_QiOPoQ_Supplement_theorem_6_7
-- name    : QiOPoQ.Supplement.theorem_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:16:49.318199+00:00
-- url     : https://prove2.me/theorems/027b4021-0e09-48d4-b254-3e5ca7f0d8fe
-- title:
--   Theorem 6.7: qiO for ancilla-free unitary circuits gives classical polynomial-time qiO for tidy unitary circuits
-- statement:
--   Suppose there is qiO in the sense of Definition 3.2 for all polynomial-size ancilla-free unitary circuits of width at least $\lambda$. Then there is a classical polynomial-time qiO for polynomial-size tidy unitary circuits.
--
--   Precisely, over a finite universal gate set: if some classical PPT obfuscator is correct (Definition 3.1) and qiO-secure (Definition 3.2) for polynomial-size ancilla-free unitary families of width at least $\lambda$, then some classical PPT obfuscator is correct and qiO-secure for polynomial-size tidy unitary families. This holds both for security against non-uniform classical PPT adversaries and for security against non-uniform QPT adversaries, each kind in hypothesis and conclusion alike.
--
--   Together with Corollary 6.8 this lifts ancilla-free qiO to qiO for $\mathcal C_{\mathsf{BQP}}$.
--
--   Differences from the source:
--   - reading: a fixed finite universal gate set (§3.1), synthesis by [BBC+95], [DN06] → IsUniversal G: every unitary on n qubits is approximated in operator norm, up to global phase, by an ancilla-free circuit over G, and every gate entry is computable to m bits in time poly(m); reason: the standard meaning of a finite universal gate set, with the computability premise of the Solovay–Kitaev algorithm the proof cites; every concrete gate set (e.g. Clifford+T) satisfies it
--   - reading: qiO in the sense of Definition 3.2 (adversary class not fixed) → two conjuncts: classical-secure ⇒ classical-secure and quantum-secure ⇒ quantum-secure; reason: Definition 3.2 leaves the kind open ('Depending on whether we quantify A over all PPT or QPT algorithms'); the theorem is claimed for the definition as stated
--   - reading: C^{tidy}_{unitary}: n_in = n_out, n_anc = n_junk, leakage operator norm ≤ negl(λ) → IsTidyUnitary: these conditions, polynomial size, and the unitary condition of §3.1; reason: the notation C^{tidy}_{unitary} denotes the tidy subclass of C_unitary, as C^{anc-free} denotes the ancilla-free subclass
--   - encoding: the operator norm → opNorm: supremum of ∥Mv∥₂ over unit vectors v; reason: the definition of the operator norm
--   - reading: polynomial-size ancilla-free unitary circuits of width at least λ → IsAFUnitaryWide (families); reason: Definition 3.2 quantifies over families
--   - reading: non-uniform QPT algorithms (adversaries, provers, distinguishers, inverters) → NUQPT: classical advice of polynomial length, coins, a classical polynomial-time generator of circuits over the gate set run on |0…0⟩ and measured, and classical polynomial-time post-processing; reason: the paper never uses quantum advice and excludes quantum auxiliary inputs (§3.1); over a universal gate set adaptivity and intermediate measurements can be deferred into the circuits
--   - encoding: PPT algorithms and classical polynomial-time algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count (and advice for non-uniform ones), on fixed self-delimiting encodings; reason: the standard model; same instances as the base mission
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 6.7, p.34; §3.1, p.13 (tidy unitary circuits); Notation 6.1, p.30

import Mathlib
import Definitions.Def_QiOPoQ_Supplement_IsUniversal
import Definitions.Def_QiOPoQ_Supplement_IsObfCorrectOn
import Definitions.Def_QiOPoQ_Supplement_IsQiOClassicalOn
import Definitions.Def_QiOPoQ_Supplement_IsQiOQuantumOn
import Definitions.Def_QiOPoQ_Supplement_IsAFUnitaryWide
import Definitions.Def_QiOPoQ_Supplement_IsTidyUnitary

set_option autoImplicit false

open QAlgorithms.Complexity

namespace QiOPoQ.Supplement

/-- **Theorem 6.7 (Ancilla-free qiO implies qiO for tidy circuits).** Gheorghiu, Gupte,
Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*,
arXiv:2609.40289 (sha256 fe2f9210…), Theorem 6.7, p.34: "Suppose there is qiO in the sense of
Definition 3.2 for all polynomial-size ancilla-free unitary circuits of width at least λ. Then
there is a classical polynomial-time qiO for polynomial-size tidy unitary circuits."

Over a finite universal gate set `G`: if some classical PPT obfuscator is correct (Definition 3.1)
and qiO-secure (Definition 3.2) for polynomial-size ancilla-free unitary families of width at least
`λ`, then some classical PPT obfuscator is correct and qiO-secure for polynomial-size tidy unitary
families; this holds for security against non-uniform classical PPT adversaries (first conjunct)
and against non-uniform QPT adversaries (second conjunct).

**Formalization Note.** "qiO in the sense of Definition 3.2" does not fix the adversary class
("Depending on whether we quantify A over all PPT or QPT algorithms", p.14), so both readings are
stated, each with the same kind of security in hypothesis and conclusion. Universality is the
paper's standing gate-set assumption (§3.1, Notation 6.1), used by the proof's gate synthesis. -/
theorem theorem_6_7 (G : GateSet) (hG : IsUniversal G) :
    ((∃ Obf : UPPT, IsObfCorrectOn G IsAFUnitaryWide Obf ∧ IsQiOClassicalOn G IsAFUnitaryWide Obf) →
      ∃ Obf' : UPPT, IsObfCorrectOn G IsTidyUnitary Obf' ∧ IsQiOClassicalOn G IsTidyUnitary Obf') ∧
    ((∃ Obf : UPPT, IsObfCorrectOn G IsAFUnitaryWide Obf ∧ IsQiOQuantumOn G IsAFUnitaryWide Obf) →
      ∃ Obf' : UPPT, IsObfCorrectOn G IsTidyUnitary Obf' ∧ IsQiOQuantumOn G IsTidyUnitary Obf') := by sorry

end QiOPoQ.Supplement
