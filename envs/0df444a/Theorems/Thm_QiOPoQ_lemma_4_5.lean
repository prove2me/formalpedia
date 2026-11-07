-- Prove2me | Theorems.Thm_QiOPoQ_lemma_4_5
-- name    : QiOPoQ.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:07.228144+00:00
-- url     : https://prove2.me/theorems/a8be1f66-8ae7-4f71-ac22-01ba8eb0b099
-- title:
--   Lemma 4.5: qiO and BQP ⊄ i.o.P/poly give one-way functions
-- statement:
--   Suppose $\mathsf{BQP}\not\subseteq$ i.o.P/poly and that there exists an obfuscation scheme for $\mathcal C_{\mathsf{BQP}}$ satisfying qiO security against classical polynomial-time adversaries. Precisely: let Obf be a classical PPT obfuscator for $\mathcal C_{\mathsf{BQP}}$ with qiO security against non-uniform classical PPT adversaries, and let $L\notin$ i.o.P/poly be decided with negligible error by uniformly generated circuits $V_\lambda$. Then there is a one-way function secure against non-uniform classical PPT algorithms.
--
--   This is why Theorem 4.7 needs no assumption on one-way functions: public verification comes for free.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any finite gate set with designated I, X, CNOT and an adjoint map; reason: no step uses universality; every universal gate set of the required form is an instance
--   - reading: BQP ⊄ i.o.P/poly, with Notation 4.1 choosing L ∈ BQP \ i.o.P/poly and V_λ → for every L ∉ i.o.P/poly decided by uniformly generated V_λ with negligible error and an ancilla output wire; reason: the construction is built from this datum (Notation 4.1, proof of Lemma 4.4); the universal quantifier covers whichever choice is made
--   - reading: C_BQP: for C of description length λ, ∥C − X^{b_C}(·)∥⋄ ≤ negl(λ) → membership of polynomial-size families, with one negligible function per family; reason: negl(λ) has a meaning only for a family; Definition 3.2 quantifies over polynomial-size families
--   - encoding: PPT and non-uniform algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count, a polynomially bounded advice string, and fixed self-delimiting encodings; reason: the standard model; a machine using at most p coins reads exactly p
--   - encoding: ∥·∥⋄, normalization not fixed by the paper → supremum over pure states with a same-size reference, no factor ½; reason: a constant factor does not affect ≤ negl(λ)
--   - encoding: a one-way function family {f_λ}, f_λ with input length λ, f := f_t → one polynomial-time map f on all strings (f_λ = f on length λ), inverted successfully by any preimage of any length; Figure 6 applies f to the t(λ)-bit string b; reason: the standard notion of a one-way function; same instances
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Lemma 4.5, p.20

import Mathlib
import Definitions.Def_QiOPoQ_IsObfCorrect
import Definitions.Def_QiOPoQ_IsQiOClassical
import Definitions.Def_QiOPoQ_IsOWF
import Definitions.Def_QiOPoQ_samplerTV
import Definitions.Def_QiOPoQ_IOPpoly
import Definitions.Def_QiOPoQ_IsDecider
import Definitions.Def_QiOPoQ_IsPadding
import Definitions.Def_QiOPoQ_IsAdmissibleRounds
set_option autoImplicit false
open QAlgorithms.Complexity

namespace QiOPoQ

/-- **Lemma 4.5.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Lemma 4.5, p.20: "Suppose that BQP ⊄ i.o.P/poly and that there exists
an obfuscation scheme for C_BQP satisfying qiO security against classical polynomial-time
adversaries. Then, there exist one-way functions that are secure against classical PPT
algorithms."

**Formalization Note.** The obfuscation scheme is a classical PPT `Obf` that is an obfuscator
for C_BQP (Definition 3.1, `IsObfCorrect`) with qiO security against non-uniform classical PPT
adversaries (Definition 3.2, `IsQiOClassical`). BQP ⊄ i.o.P/poly enters as the Notation 4.1 datum:
a language `L ∉ i.o.P/poly` decided by uniformly generated circuits `V_λ` with negligible error
(`IsDecider`); the padding `C_{b,λ}` used in the proof is not assumed. -/
theorem lemma_4_5 (G : GateSet) (Obf : UPPT) (hcorr : IsObfCorrect G Obf)
    (hqiO : IsQiOClassical G Obf) (L : Set Str) (V : ℕ → Circ G) (hV : IsDecider G L V)
    (hL : ¬ IOPpoly L) :
    ∃ f : Str → Str, IsOWF f := by sorry

end QiOPoQ
