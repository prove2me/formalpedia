-- Prove2me | Theorems.Thm_QiOPoQ_theorem_4_7_completeness
-- name    : QiOPoQ.theorem_4_7_completeness
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:53.049439+00:00
-- url     : https://prove2.me/theorems/f069c769-cb07-4947-abc4-a8b60e693056
-- title:
--   Theorem 4.7, proof: completeness of Figure 6
-- statement:
--   Let Obf be an obfuscator for $\mathcal C_{\mathsf{BQP}}$ (correctness only), let $C_{b,\lambda}$ be a padding, $f$ any function, $t$ admissible and $\ell$ an adequate coin polynomial. Then the honest quantum prover of Figure 6 is accepted with probability at least $1-\mu(\lambda)$ for a negligible $\mu$: the completeness clause of Definition 3.3.
--
--   Only correctness of the obfuscator and $t\le\mathrm{poly}(\lambda)$ enter: neither qiO security, the hardness of $L$, nor one-wayness of $f$.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any finite gate set with designated I, X, CNOT and an adjoint map; reason: no step uses universality; every universal gate set of the required form is an instance
--   - generalization: C_{b,λ}: "Pad C_{b,λ} so that it has the required gate count", no specific padding → every family with the printed shape, output wire, channel X^b(·) and polynomial-time construction; reason: specializes to whichever padding is chosen
--   - reading: C_BQP: for C of description length λ, ∥C − X^{b_C}(·)∥⋄ ≤ negl(λ) → membership of polynomial-size families, with one negligible function per family; reason: negl(λ) has a meaning only for a family; Definition 3.2 quantifies over polynomial-size families
--   - encoding: random tapes r_i ∈ {0,1}^{poly(λ)}, with a polynomial ℓ → tapes of the larger of Obf’s coin counts on the two padded inputs, for every polynomial ℓ with ℓ ≥ t + t·|r_i|; surplus coins ignored; reason: same output law; ℓ stays a polynomial
--   - encoding: Prove is quantum polynomial time and evaluates each Ĉ_i on |0⟩ → a classical polynomial-time generator of the list of circuits, each run on all zeros, with measured outputs concatenated in order; reason: the standard uniform-generator model of QPT
--   - generalization: the hypotheses of Theorem 4.7 (BQP ⊄ i.o.P/poly, a correct and qiO-secure obfuscation scheme) and a one-way f → correctness of Obf (IsObfCorrect) only; V_λ any circuit family with a padding, f any function; reason: "Completeness holds by the correctness of the qiO scheme"; every instance of Theorem 4.7 satisfies these hypotheses
--   - reading: t := t(λ) with t ≤ poly(λ), t ≥ Ω(λ) (Notation 4.1) → t computable from 1^λ in polynomial time, t(λ) ≤ p(λ) for a polynomial p, and ∃ c > 0, ∃ N, ∀ λ ≥ N, c·λ ≤ t(λ) (IsAdmissibleRounds); reason: Ω(λ) in its usual sense; computability is implied because Challenge and Verify are classical polynomial-time (Definition 3.3) and must compute t
--   - encoding: Figure 6: Verify(1^λ, chall, resp) → Verify(1^λ, r, chall, resp) with the coins r ignored, rejecting a challenge that does not parse as t + 1 components; reason: the syntax of Definition 3.3; r is unused, as Figure 6 prints
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), proof of Theorem 4.7, p.20

import Mathlib
import Definitions.Def_QiOPoQ_IsObfCorrect
import Definitions.Def_QiOPoQ_IsQiOClassical
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

/-- **Proof of Theorem 4.7: completeness.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), proof of Theorem 4.7, p.20: "Completeness
holds by the correctness of the qiO scheme."

For an obfuscator `Obf` for C_BQP (Definition 3.1, correctness only), any padding `C_{b,λ}`
(for any circuits `V_λ`), any function `f`, any admissible number of repetitions `t` and any
adequate coin polynomial `ℓ`, the honest quantum prover of Figure 6 is accepted with probability
at least `1 − μ(λ)` for a negligible `μ` (completeness of Definition 3.3).

**Formalization Note.** Only correctness of the obfuscator and `t ≤ poly(λ)` are used; neither
qiO security, nor the hardness of `L`, nor one-wayness of `f` enters completeness. -/
theorem theorem_4_7_completeness (G : GateSet) (Obf : UPPT) (hcorr : IsObfCorrect G Obf)
    (V : ℕ → Circ G) (Cb : Bool → ℕ → Circ G) (hCb : IsPadding V Cb) (f : Str → Str)
    (t : ℕ → ℕ) (ht : IsAdmissibleRounds t) (ℓ : Polynomial ℕ) (hℓ : AdequateCoins Obf Cb t ℓ) :
    PoQComplete G ℓ (fig6Challenge Obf Cb f t) (fig6Prove t) (fig6Verify f t) := by sorry

end QiOPoQ
