-- Prove2me | Theorems.Thm_QiOPoQ_Supplement_theorem_4_3
-- name    : QiOPoQ.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:11:22.244476+00:00
-- url     : https://prove2.me/theorems/2d34ef9f-65ea-4d40-acfc-27b974ca7ec0
-- title:
--   Theorem 4.3: qiO and BQP ⊄ i.o.P/poly make Figure 4 a secure two-message proof of quantumness
-- statement:
--   Suppose that $\mathsf{BQP}\not\subseteq$ i.o.P/poly and that there is a qiO scheme for $\mathcal C_{\mathsf{BQP}}$ that is secure against classical polynomial-time adversaries. Then the protocol in Figure 4 is a secure two-message proof of quantumness.
--
--   Precisely, fix a gate set containing $I$, $X$, CNOT and closed under adjoints, a classical PPT obfuscator Obf for $\mathcal C_{\mathsf{BQP}}$ (Definition 3.1) with qiO security against non-uniform classical PPT adversaries (Definition 3.2), and a language $L\notin$ i.o.P/poly (Definition 4.2) decided with negligible error by uniformly generated circuits $V_\lambda$ (Notation 4.1). Then:
--
--   1. a padding $C_{b,\lambda}$ of Notation 4.1 and an admissible number of repetitions $t$ exist; and
--   2. for every padding $C_{b,\lambda}$ and every admissible $t$ ($t\le\mathrm{poly}(\lambda)$, $t\ge\Omega(\lambda)$, computable from $1^\lambda$), an adequate coin polynomial exists, and for every adequate polynomial $\ell$ the protocol of Figure 4 — challenge $(\hat C_1,\dots,\hat C_t)$ with $\hat C_i=\mathrm{qiO}(1^\lambda,C_{b_i,\lambda};r_i)$, the honest prover that evaluates each $\hat C_i$ on $|0\rangle$, and the verifier that accepts iff the response equals $(b_1,\dots,b_t)$ — satisfies Definition 3.3: syntax, completeness, and soundness against every non-uniform classical PPT prover.
--
--   This is the privately verifiable protocol from which the mission's goal, Theorem 4.7, is obtained by publishing $f(b)$.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any gate set with designated I, X, CNOT and an adjoint map (QiOPoQ.GateSet); reason: the statement for every such gate set specializes to the paper's fixed one; the adversary model is taken over the same gate set
--   - reading: BQP ⊄ i.o.P/poly, with Notation 4.1 choosing L ∈ BQP \ i.o.P/poly and V_λ → for every L ∉ i.o.P/poly decided by uniformly generated V_λ with negligible error and an ancilla output wire (IsDecider ∧ ¬IOPpoly); reason: the construction is built from this datum (Notation 4.1); the universal quantifier covers whichever choice is made; same as the published goal
--   - generalization: C_{b,λ}: 'Pad C_{b,λ} so that it has the required gate count', no specific padding → every padding with the printed shape, output wire, channel X^b(·) and polynomial-time construction (IsPadding); reason: specializes to whichever padding is chosen
--   - reading: C_BQP: for C of description length λ, ∥C − X^{b_C}(·)∥⋄ ≤ negl(λ) → membership of polynomial-size families (published InCBQP), one negligible function per family; reason: negl(λ) has a meaning only for a family; the base mission's reading
--   - encoding: PPT algorithms and classical polynomial-time algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count (and advice for non-uniform ones), on fixed self-delimiting encodings; reason: the standard model; same instances as the base mission
--   - encoding: ∥·∥⋄, normalization not fixed by the paper → the published diamond: supremum over pure states with a same-size reference, no factor ½; reason: a constant factor does not affect ≤ negl(λ)
--   - encoding: random tapes r_i ∈ {0,1}^{poly(λ)} and a polynomial ℓ → tapes of fig6Block coins, for every polynomial ℓ with ℓ ≥ t + t·|r_i| (AdequateCoins); surplus coins ignored; reason: same output law; ℓ stays a polynomial
--   - encoding: Prove evaluates each obfuscated circuit on |0⟩ and returns the measured outputs → the published fig6Prove with t = t: the classical list of the first t challenge components, each run on all zeros, outcomes concatenated in order; reason: the uniform-generator model of QPT used by the base mission
--   - generalization: Notation 4.1 presupposes that C_{b,λ} and t can be chosen → the existence of a padding and of an admissible t is stated as a first clause; reason: makes the second clause non-vacuous under the hypotheses alone; specializes to Theorem 4.3
--   - reading: t ≤ poly(λ), t ≥ Ω(λ) (Notation 4.1) → IsAdmissibleRounds: t computable from 1^λ in polynomial time, t ≤ p(λ), and ∃ c > 0 with c·λ ≤ t(λ) for all large λ; reason: Ω(λ) in its usual sense; Challenge and Verify must compute t
--   - encoding: Verify: recover (b_1, …, b_t) from r, parse resp = (b′_1, …, b′_t) → accept iff resp equals the first t coins; a response of another length is rejected; chall unused; reason: the printed test; an unparsable response is rejected
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 4.3, p.18; Figure 4 and Notation 4.1, p.17

import Mathlib
import Definitions.Def_QiOPoQ_IsObfCorrect
import Definitions.Def_QiOPoQ_IsQiOClassical
import Definitions.Def_QiOPoQ_IOPpoly
import Definitions.Def_QiOPoQ_IsDecider
import Definitions.Def_QiOPoQ_IsPadding
import Definitions.Def_QiOPoQ_IsAdmissibleRounds
import Definitions.Def_QiOPoQ_IsTwoMsgPoQ
import Definitions.Def_QiOPoQ_fig6Challenge
import Definitions.Def_QiOPoQ_fig6Prove
import Definitions.Def_QiOPoQ_Supplement_fig4Challenge
import Definitions.Def_QiOPoQ_Supplement_fig4Verify

set_option autoImplicit false

open QAlgorithms.Complexity

namespace QiOPoQ.Supplement

/-- **Theorem 4.3.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and
Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Theorem 4.3,
p.18: "Suppose that BQP ⊄ i.o.P/poly and that there is a qiO scheme for C_BQP that is secure
against classical polynomial-time adversaries. Then, the protocol in Figure 4 is a secure
two-message proof of quantumness."

Let `G` be a gate set with `I, X, CNOT` closed under adjoints, `Obf` a classical PPT obfuscator
for C_BQP (Definition 3.1) with qiO security against non-uniform classical PPT adversaries
(Definition 3.2), and `(L, V)` a Notation 4.1 datum: `L ∉ i.o.P/poly` decided with negligible
error by uniformly generated circuits `V_λ`. Then a padding `C_{b,λ}` of Notation 4.1 and an
admissible `t` exist, and for every padding `C_{b,λ}` and every admissible `t` (`t ≤ poly(λ)`,
`t ≥ Ω(λ)`, computable from `1^λ`) an adequate coin polynomial `ℓ` exists and, for every adequate
`ℓ`, the protocol of Figure 4 (Challenge `fig4Challenge`, the honest prover `fig6Prove t`, which
runs the `t` challenge circuits, and Verify `fig4Verify`) is a two-message proof of quantumness
(Definition 3.3: syntax, completeness, soundness against every non-uniform classical PPT prover).

**Formalization Note.** BQP ⊄ i.o.P/poly enters through the Notation 4.1 datum, universally
quantified, exactly as in the published goal `QiOPoQ.theorem_4_7_public_poq`. The existence of a
padding and of `t` records that Notation 4.1 can be carried out, so the second clause is not
vacuous. -/
theorem theorem_4_3 (G : GateSet) (Obf : UPPT) (hcorr : IsObfCorrect G Obf)
    (hqiO : IsQiOClassical G Obf) (L : Set Str) (V : ℕ → Circ G) (hV : IsDecider G L V)
    (hL : ¬ IOPpoly L) :
    (∃ Cb : Bool → ℕ → Circ G, IsPadding V Cb) ∧ (∃ t : ℕ → ℕ, IsAdmissibleRounds t) ∧
    ∀ Cb : Bool → ℕ → Circ G, IsPadding V Cb → ∀ t : ℕ → ℕ, IsAdmissibleRounds t →
      (∃ ℓ : Polynomial ℕ, AdequateCoins Obf Cb t ℓ) ∧
      ∀ ℓ : Polynomial ℕ, AdequateCoins Obf Cb t ℓ →
        IsTwoMsgPoQ G ℓ (fig4Challenge Obf Cb t) (fig6Prove t) (fig4Verify t) := by sorry

end QiOPoQ.Supplement
