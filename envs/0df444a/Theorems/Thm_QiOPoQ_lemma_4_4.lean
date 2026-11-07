-- Prove2me | Theorems.Thm_QiOPoQ_lemma_4_4
-- name    : QiOPoQ.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:27.532194+00:00
-- url     : https://prove2.me/theorems/25f1ffa5-bf18-4daf-86df-5f11ce142d12
-- title:
--   Lemma 4.4: obfuscations of $C_{0,\lambda}$ and $C_{1,\lambda}$ are indistinguishable
-- statement:
--   Let Obf have qiO security against classical adversaries, let $L\notin$ i.o.P/poly be decided by $V_\lambda$, and let $C_{b,\lambda}$ be a padding. Then $\{C_{0,\lambda}\}$ and $\{C_{1,\lambda}\}$ are in $\mathcal C_{\mathsf{BQP}}$, are efficiently constructible, have the same shape for every $\lambda$, and induce the channels $I(\cdot)$ and $X(\cdot)$ respectively. Further, for every non-uniform classical PPT adversary $A$ there is a negligible $\mu$ with, for every $\lambda$,
--
--   $$
--   \big|\Pr[A(1^\lambda,\mathrm{qiO}(1^\lambda,C_{0,\lambda}))=1]-\Pr[A(1^\lambda,\mathrm{qiO}(1^\lambda,C_{1,\lambda}))=1]\big|\le\mu(\lambda).
--   $$
--
--   This is the one place where the two channels, which are entirely different, are shown to have indistinguishable obfuscations.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any finite gate set with designated I, X, CNOT and an adjoint map; reason: no step uses universality; every universal gate set of the required form is an instance
--   - reading: BQP ⊄ i.o.P/poly, with Notation 4.1 choosing L ∈ BQP \ i.o.P/poly and V_λ → for every L ∉ i.o.P/poly decided by uniformly generated V_λ with negligible error and an ancilla output wire; reason: the construction is built from this datum (Notation 4.1, proof of Lemma 4.4); the universal quantifier covers whichever choice is made
--   - generalization: C_{b,λ}: "Pad C_{b,λ} so that it has the required gate count", no specific padding → every family with the printed shape, output wire, channel X^b(·) and polynomial-time construction; reason: specializes to whichever padding is chosen
--   - reading: C_BQP: for C of description length λ, ∥C − X^{b_C}(·)∥⋄ ≤ negl(λ) → membership of polynomial-size families, with one negligible function per family; reason: negl(λ) has a meaning only for a family; Definition 3.2 quantifies over polynomial-size families
--   - encoding: PPT and non-uniform algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count, a polynomially bounded advice string, and fixed self-delimiting encodings; reason: the standard model; a machine using at most p coins reads exactly p
--   - encoding: ∥·∥⋄, normalization not fixed by the paper → supremum over pure states with a same-size reference, no factor ½; reason: a constant factor does not affect ≤ negl(λ)
--   - encoding: "efficiently constructible by a classical PPT algorithm" → a deterministic polynomial-time map (b, 1^λ) ↦ the description of C_{b,λ}; reason: deterministic is a special case of PPT and is what the padding provides
--   - generalization: "Suppose the hypotheses for Theorem 4.3 hold": a qiO scheme for C_BQP (an obfuscator, correct by Definition 3.1, with qiO security) → qiO security (IsQiOClassical) only; correctness of the obfuscator is not assumed; reason: the proof of Lemma 4.4 uses only security; every correct and secure scheme is an instance
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Lemma 4.4, p.18, eq. (2)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_IsObfCorrect
import Definitions.Def_QiOPoQ_IsQiOClassical
import Definitions.Def_QiOPoQ_IOPpoly
import Definitions.Def_QiOPoQ_IsDecider
import Definitions.Def_QiOPoQ_IsPadding
import Definitions.Def_QiOPoQ_IsAdmissibleRounds
set_option autoImplicit false
open QAdvFew.PoQOracle QAlgorithms.Complexity

namespace QiOPoQ

/-- **Lemma 4.4.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Lemma 4.4, p.18: "Suppose the hypotheses for Theorem 4.3 hold. Then,
the circuit families {C_{0,λ}}λ∈N and {C_{1,λ}}λ∈N defined in Notation 4.1 are in C_BQP, are
efficiently constructible by a classical PPT algorithm, have the same shape, and induce the
channels I(·) and X(·) respectively. Further, for every classical PPT adversary A and every
λ ∈ N, |Pr[A(1^λ, qiO(1^λ, C_{0,λ})) = 1] − Pr[A(1^λ, qiO(1^λ, C_{1,λ})) = 1]| ≤ negl(λ). (2)"

**Formalization Note.** The hypotheses of Theorem 4.3 are qiO security against classical
adversaries and BQP ⊄ i.o.P/poly, the latter entering through the Notation 4.1 datum: a language
`L ∉ i.o.P/poly` with deciders `V_λ` (`IsDecider`), and any padding `C_{b,λ}` (`IsPadding`).
`I(·)` is `bitFlip false`, `X(·)` is `bitFlip true`. -/
theorem lemma_4_4 (G : GateSet) (Obf : UPPT) (hqiO : IsQiOClassical G Obf) (L : Set Str)
    (V : ℕ → Circ G) (hV : IsDecider G L V) (hL : ¬ IOPpoly L) (Cb : Bool → ℕ → Circ G)
    (hCb : IsPadding V Cb) :
    InCBQP (Cb false) ∧ InCBQP (Cb true) ∧
    (∃ g : Str → Str, PolyTimeComputable g ∧ ∀ b n, g (pair [b] (unary n)) = encCirc (Cb b n)) ∧
    (∀ n, shape (Cb false n) = shape (Cb true n)) ∧
    (∀ n, chanAs (Cb false n) 1 1 = bitFlip false ∧ chanAs (Cb true n) 1 1 = bitFlip true) ∧
    ∀ A : NUPPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n,
      |obfAcc Obf A n (Cb false n) - obfAcc Obf A n (Cb true n)| ≤ μ n := by sorry

end QiOPoQ
