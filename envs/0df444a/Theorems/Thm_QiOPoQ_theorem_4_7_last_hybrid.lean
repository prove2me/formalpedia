-- Prove2me | Theorems.Thm_QiOPoQ_theorem_4_7_last_hybrid
-- name    : QiOPoQ.theorem_4_7_last_hybrid
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:05:52.050378+00:00
-- url     : https://prove2.me/theorems/ea6471e9-773f-4c62-8d02-8e4f51012957
-- title:
--   Theorem 4.7, proof: $p_{2t}\le\mathrm{negl}(\lambda)$
-- statement:
--   Let Obf be a classical PPT algorithm, let $C_{b,\lambda}$ be a padding, $f$ a one-way function secure against non-uniform classical PPT algorithms and $t$ admissible. For every non-uniform classical PPT adversary $A$,
--
--   $$
--   \lambda\mapsto p_{2t(\lambda)}(\lambda)
--   $$
--
--   is negligible: in the hybrid $H_{2t}$ the obfuscated circuits are independent of the one-way function challenge $f(b)$.
--
--   The function is attacked at input length $t(\lambda)$, and $t\ge c\lambda$ eventually (Notation 4.1) is what makes a negligible function of $t(\lambda)$ negligible in $\lambda$.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any finite gate set with designated I, X, CNOT and an adjoint map; reason: no step uses universality; every universal gate set of the required form is an instance
--   - generalization: C_{b,λ}: "Pad C_{b,λ} so that it has the required gate count", no specific padding → every family with the printed shape, output wire, channel X^b(·) and polynomial-time construction; reason: specializes to whichever padding is chosen
--   - encoding: PPT and non-uniform algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count, a polynomially bounded advice string, and fixed self-delimiting encodings; reason: the standard model; a machine using at most p coins reads exactly p
--   - generalization: the hypotheses of Theorem 4.7 (BQP ⊄ i.o.P/poly, a correct and qiO-secure scheme) → Obf any classical PPT algorithm and V_λ any circuit family with a padding; no correctness, no security, no hypothesis on L; reason: p_{2t} ≤ negl uses only one-wayness of f, t ≥ Ω(λ) and that the inverter can sample the obfuscations of C_{0,λ}; every instance of Theorem 4.7 is covered
--   - reading: t := t(λ) with t ≤ poly(λ), t ≥ Ω(λ) (Notation 4.1) → t computable from 1^λ in polynomial time, t(λ) ≤ p(λ) for a polynomial p, and ∃ c > 0, ∃ N, ∀ λ ≥ N, c·λ ≤ t(λ) (IsAdmissibleRounds); reason: Ω(λ) in its usual sense; computability is implied because Challenge and Verify are classical polynomial-time (Definition 3.3) and must compute t
--   - encoding: a one-way function family {f_λ}, f_λ with input length λ, f := f_t → one polynomial-time map f on all strings (f_λ = f on length λ), inverted successfully by any preimage of any length; Figure 6 applies f to the t(λ)-bit string b; reason: the standard notion of a one-way function; same instances
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), proof of Theorem 4.7, p.22

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_IsOWF
import Definitions.Def_QiOPoQ_samplerTV
import Definitions.Def_QiOPoQ_IsDecider
import Definitions.Def_QiOPoQ_IsPadding
import Definitions.Def_QiOPoQ_IsAdmissibleRounds
import Definitions.Def_QiOPoQ_hybProb
set_option autoImplicit false
open QAdvFew.PoQOracle QAlgorithms.Complexity

namespace QiOPoQ

/-- **Proof of Theorem 4.7: the last hybrid.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), proof of Theorem 4.7, p.22: "In Hybrid
H_{2t}, the obfuscated circuits in the challenge are independent of the one-way function
challenge, so by the one-way security of f against classical adversaries, p_{2t} ≤ negl(λ)."

For any padding `C_{b,λ}` (for any circuits `V_λ`), any one-way function `f` secure against
non-uniform classical PPT algorithms, any admissible `t` and any non-uniform classical PPT `A`,
`λ ↦ p_{2t(λ)}(λ)` is negligible.

**Formalization Note.** The one-way function is attacked at input length `t(λ)`; `t ≥ cλ`
eventually (Notation 4.1's `Ω(λ)`) is what makes a negligible function of `t(λ)` negligible in
`λ`. No property of the obfuscator beyond being a classical PPT algorithm is used. -/
theorem theorem_4_7_last_hybrid (G : GateSet) (Obf : UPPT) (V : ℕ → Circ G)
    (Cb : Bool → ℕ → Circ G) (hCb : IsPadding V Cb) (f : Str → Str) (hf : IsOWF f)
    (t : ℕ → ℕ) (ht : IsAdmissibleRounds t) (A : NUPPT) :
    Negligible fun n => hybProb Obf Cb f t A n (2 * t n) := by sorry

end QiOPoQ
