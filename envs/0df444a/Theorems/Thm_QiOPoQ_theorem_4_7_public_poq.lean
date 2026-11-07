-- Prove2me | Theorems.Thm_QiOPoQ_theorem_4_7_public_poq
-- name    : QiOPoQ.theorem_4_7_public_poq
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:09:18.627317+00:00
-- url     : https://prove2.me/theorems/8433dc25-dc6d-45e2-b674-6a6298f6e032
-- title:
--   Theorem 4.7 with Lemma 4.5: qiO and BQP ⊄ i.o.P/poly give a publicly verifiable two-message proof of quantumness
-- statement:
--   Suppose that $\mathsf{BQP}\not\subseteq$ i.o.P/poly, and that there exists an obfuscation scheme for $\mathcal C_{\mathsf{BQP}}$ satisfying qiO security against classical polynomial-time adversaries. Then the protocol of Figure 6 is a secure publicly verifiable two-message proof of quantumness.
--
--   Precisely, fix a gate set containing $I$, $X$, CNOT and closed under adjoints, a classical PPT obfuscator Obf for $\mathcal C_{\mathsf{BQP}}$ (Definition 3.1) with qiO security against non-uniform classical PPT adversaries (Definition 3.2), and a language $L\notin$ i.o.P/poly (Definition 4.2) decided with negligible error by uniformly generated circuits $V_\lambda$ (Notation 4.1). Then:
--
--   1. a one-way function secure against non-uniform classical PPT algorithms exists (Lemma 4.5), a padding $C_{b,\lambda}$ of Notation 4.1 exists, and an admissible $t$ exists; and
--   2. for every padding $C_{b,\lambda}$, every such one-way function $f$ and every admissible $t$, an adequate coin polynomial exists, and for every adequate polynomial $\ell$ the protocol (Challenge, Prove, Verify) of Figure 6 satisfies Definition 3.3 (syntax, completeness, and soundness against every non-uniform classical PPT prover) and Definition 3.4.
--
--   Clause 1 is what makes the theorem's hypotheses alone suffice: no one-way function needs to be assumed.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any finite gate set with designated I, X, CNOT and an adjoint map; reason: no step uses universality; every universal gate set of the required form is an instance
--   - reading: BQP ⊄ i.o.P/poly, with Notation 4.1 choosing L ∈ BQP \ i.o.P/poly and V_λ → for every L ∉ i.o.P/poly decided by uniformly generated V_λ with negligible error and an ancilla output wire; reason: the construction is built from this datum (Notation 4.1, proof of Lemma 4.4); the universal quantifier covers whichever choice is made
--   - generalization: C_{b,λ}: "Pad C_{b,λ} so that it has the required gate count", no specific padding → every family with the printed shape, output wire, channel X^b(·) and polynomial-time construction; reason: specializes to whichever padding is chosen
--   - reading: C_BQP: for C of description length λ, ∥C − X^{b_C}(·)∥⋄ ≤ negl(λ) → membership of polynomial-size families, with one negligible function per family; reason: negl(λ) has a meaning only for a family; Definition 3.2 quantifies over polynomial-size families
--   - encoding: PPT and non-uniform algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count, a polynomially bounded advice string, and fixed self-delimiting encodings; reason: the standard model; a machine using at most p coins reads exactly p
--   - encoding: ∥·∥⋄, normalization not fixed by the paper → supremum over pure states with a same-size reference, no factor ½; reason: a constant factor does not affect ≤ negl(λ)
--   - encoding: random tapes r_i ∈ {0,1}^{poly(λ)}, with a polynomial ℓ → tapes of the larger of Obf’s coin counts on the two padded inputs, for every polynomial ℓ with ℓ ≥ t + t·|r_i|; surplus coins ignored; reason: same output law; ℓ stays a polynomial
--   - encoding: Prove is quantum polynomial time and evaluates each Ĉ_i on |0⟩ → a classical polynomial-time generator of the list of circuits, each run on all zeros, with measured outputs concatenated in order; reason: the standard uniform-generator model of QPT
--   - generalization: Theorem 4.7 asserts security of Section 4.2; Lemma 4.5 and Notation 4.1 state or presuppose the ingredients separately → the existence of a one-way function, a padding and an admissible t is stated as a first clause of the goal, next to the security of the protocol for every choice of them; reason: specializes to Theorem 4.7; Figure 6 is thereby instantiable under the hypotheses alone, as p.20 says
--   - reading: t := t(λ) with t ≤ poly(λ), t ≥ Ω(λ) (Notation 4.1) → t computable from 1^λ in polynomial time, t(λ) ≤ p(λ) for a polynomial p, and ∃ c > 0, ∃ N, ∀ λ ≥ N, c·λ ≤ t(λ) (IsAdmissibleRounds); reason: Ω(λ) in its usual sense; computability is implied because Challenge and Verify are classical polynomial-time (Definition 3.3) and must compute t
--   - encoding: a one-way function family {f_λ}, f_λ with input length λ, f := f_t → one polynomial-time map f on all strings (f_λ = f on length λ), inverted successfully by any preimage of any length; Figure 6 applies f to the t(λ)-bit string b; reason: the standard notion of a one-way function; same instances
--   - encoding: Figure 6: Verify(1^λ, chall, resp) → Verify(1^λ, r, chall, resp) with the coins r ignored, rejecting a challenge that does not parse as t + 1 components; reason: the syntax of Definition 3.3; r is unused, as Figure 6 prints
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 4.7 and Lemma 4.5, p.20; Figure 6, p.21; Notation 4.1, p.17

import Mathlib
import Definitions.Def_QiOPoQ_IsObfCorrect
import Definitions.Def_QiOPoQ_IsQiOClassical
import Definitions.Def_QiOPoQ_IsOWF
import Definitions.Def_QiOPoQ_samplerTV
import Definitions.Def_QiOPoQ_IOPpoly
import Definitions.Def_QiOPoQ_IsDecider
import Definitions.Def_QiOPoQ_IsPadding
import Definitions.Def_QiOPoQ_IsAdmissibleRounds
import Definitions.Def_QiOPoQ_IsTwoMsgPoQ
import Definitions.Def_QiOPoQ_IsPubliclyVerifiable
import Definitions.Def_QiOPoQ_fig6Challenge
import Definitions.Def_QiOPoQ_fig6Prove
import Definitions.Def_QiOPoQ_fig6Verify
set_option autoImplicit false
open QAlgorithms.Complexity

namespace QiOPoQ

/-- **Theorem 4.7, with Lemma 4.5.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 4.7, p.20: "Suppose that BQP ⊄ i.o.P/poly,
and that there exists an obfuscation scheme for C_BQP satisfying qiO security against classical
polynomial-time adversaries. Then Section 4.2 is a secure publicly verifiable two-message proof of
quantumness." Lemma 4.5, p.20: under the same hypotheses "there exist one-way functions that are
secure against classical PPT algorithms"; p.20: "Let {f_λ}λ∈N be a one-way function family secure
against classical PPT algorithms … We describe our construction in Figure 6."

Let `G` be a gate set with `I, X, CNOT` closed under adjoints, `Obf` a classical PPT obfuscator
for C_BQP (Definition 3.1) with qiO security against non-uniform classical PPT adversaries
(Definition 3.2), and `(L, V)` a Notation 4.1 datum: `L ∉ i.o.P/poly` decided with negligible
error by uniformly generated circuits `V_λ`. Then
1. a one-way function secure against non-uniform classical PPT algorithms exists, a padding
   `C_{b,λ}` of Notation 4.1 exists, and an admissible `t` exists; and
2. for every padding `C_{b,λ}` of Notation 4.1, every such one-way function `f` and every
   admissible `t` (`t ≤ poly(λ)`, `t ≥ Ω(λ)`, computable from `1^λ`), an adequate coin
   polynomial `ℓ` exists, and for every adequate `ℓ` the protocol of Figure 6 is a two-message
   proof of quantumness (Definition 3.3) that is publicly verifiable (Definition 3.4).

**Formalization Note.** BQP ⊄ i.o.P/poly is used through the datum from which the protocol is
built (Notation 4.1 introduces `L`, `V_λ` and `C_{b,λ}` from it), universally quantified, so
the theorem holds for whichever datum is chosen. Clause 1 is what makes Figure 6 instantiable
under the theorem's hypotheses alone ("we get public verification for free, without having to
make any additional assumptions", p.20); the existence of a padding and of `t` records that
Notation 4.1's "define `C_{b,λ}`" and "will set `t`" can be carried out, so clause 2 is not
vacuous. -/
theorem theorem_4_7_public_poq (G : GateSet) (Obf : UPPT) (hcorr : IsObfCorrect G Obf)
    (hqiO : IsQiOClassical G Obf) (L : Set Str) (V : ℕ → Circ G) (hV : IsDecider G L V)
    (hL : ¬ IOPpoly L) :
    (∃ f : Str → Str, IsOWF f) ∧ (∃ Cb : Bool → ℕ → Circ G, IsPadding V Cb) ∧
    (∃ t : ℕ → ℕ, IsAdmissibleRounds t) ∧
    ∀ Cb : Bool → ℕ → Circ G, IsPadding V Cb → ∀ f : Str → Str, IsOWF f →
      ∀ t : ℕ → ℕ, IsAdmissibleRounds t →
        (∃ ℓ : Polynomial ℕ, AdequateCoins Obf Cb t ℓ) ∧
        ∀ ℓ : Polynomial ℕ, AdequateCoins Obf Cb t ℓ →
          IsTwoMsgPoQ G ℓ (fig6Challenge Obf Cb f t) (fig6Prove t) (fig6Verify f t) ∧
          IsPubliclyVerifiable ℓ (fig6Challenge Obf Cb f t) (fig6Verify f t) := by sorry

end QiOPoQ
