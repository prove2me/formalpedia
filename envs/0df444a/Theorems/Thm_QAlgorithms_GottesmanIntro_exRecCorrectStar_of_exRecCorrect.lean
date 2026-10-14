-- Prove2me | Theorems.Thm_QAlgorithms_GottesmanIntro_exRecCorrectStar_of_exRecCorrect
-- name    : QAlgorithms.GottesmanIntro.exRecCorrectStar_of_exRecCorrect
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T18:05:10.345784+00:00
-- url     : https://prove2.me/theorems/7fa2147a-ca25-477a-825d-40724b088f90
-- title:
--   Correctness for the ideal decoder implies correctness for a *-decoder
-- statement:
--   This lemma lets the level-reduction argument keep track of error syndromes.
--
--   Fix a fault-tolerant protocol for an $[[n,1,2t+1]]$ code with ideal decoder $\mathcal D$. A *-decoder is a unitary $W$ from one code block to one qubit together with a syndrome register $S$, such that discarding the syndrome gives the ideal decoder:
--
--   $$
--   \operatorname{Tr}_S\bigl(W\rho W^\dagger\bigr) = \mathcal D(\rho) \quad \text{for all } \rho .
--   $$
--
--   Let an ExRec of any type be given, with a fixed Pauli fault arrangement, either full or with some trailing EC steps removed. If the ExRec is correct for the ideal decoder, then it is correct for $W$:
--
--   1. Gate or wait ExRec with gate $U$ on $k$ blocks: there is a quantum operation $V$ on the $k$ syndrome registers such that $\mathcal W^{\otimes k}\circ \mathrm{EC}^{\mathrm{trail}}\circ G_U\circ \mathrm{EC}^{\mathrm{lead}} = (\mathcal U\otimes V)\circ \mathcal W^{\otimes k}\circ \mathrm{EC}^{\mathrm{lead}}$, with $\mathcal W(\rho) = W\rho W^\dagger$ (eq. (83)). The operation $V$ may depend on the faults and on $U$.
--   2. Preparation ExRec: $W\,\mathrm{EC}^{\mathrm{trail}}(\rho_{\mathrm{prep}})\,W^\dagger = |0\rangle\langle 0|\otimes\tau$ for some syndrome state $\tau$.
--   3. Measurement ExRec: the syndrome is discarded immediately, so the condition is diagram (74) with $\operatorname{Tr}_S(W\cdot W^\dagger)$ in place of $\mathcal D$.
--
--   All equalities are of superoperators.
--
--   **Formalization Note** The truncation set may be empty (the lemma as stated) or not: the source says on p.39 that Lemma 2 'also works for truncated ExRecs', and Lemma 3 uses it that way. The fault-tolerance hypothesis on the protocol is the section's standing context (the ExRec is built from fault-tolerant gadgets).
-- source:
--   Daniel Gottesman, An Introduction to Quantum Error Correction and Fault-Tolerant Quantum Computation, 2009, v1, PDF p. 38, §5.2, Lemma 2. https://arxiv.org/pdf/0904.2557v1

import Definitions.Def_QAlgorithms_Defs_FTCircuit
set_option autoImplicit false

namespace QAlgorithms.GottesmanIntro



/-- Gottesman intro p.38, Lemma 2: "If an ExRec is correct for an ideal decoder, it is correct
for a *-decoder." Let `P` be a fault-tolerant protocol and `W` a *-decoder for its ideal decoder
(a unitary from a block to one qubit ⊗ a syndrome register `Fin σ` whose syndrome-discarded
version is `P.dec`, p.37–38). For every ExRec type `κ`, every Pauli fault arrangement `F` and
every set `trunc` of removed trailing ECs (`∅` for a full ExRec; p.39: Lemma 2 "also works for
truncated ExRecs"), if the ExRec is correct for the ideal decoder then it is correct for `W`:
for a gate or wait ExRec, eq. (83) holds for some quantum operation `V` on the syndrome
registers (chosen after the faults); for a preparation ExRec, the *-decoded output is
`|0⟩⟨0| ⊗ τ` for some syndrome state `τ`; for a measurement ExRec, the syndrome is discarded. -/
theorem exRecCorrectStar_of_exRecCorrect (P : FTProtocol) (hP : P.IsFaultTolerant) {σ : ℕ}
    (W : Matrix (Bool × Fin σ) (Qubits P.n) ℂ) (hW : IsStarDecoder P.dec W) (κ : LocKind)
    (F : ExRecFaults κ) (trunc : Finset (Fin κ.trailCount)) (hcorr : ExRecCorrect P κ F trunc) :
    ExRecCorrectStar P W κ F trunc := by
  sorry


end QAlgorithms.GottesmanIntro
