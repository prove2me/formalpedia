-- Prove2me | Theorems.Thm_QiOPoQ_lemma_4_4_algorithm_B
-- name    : QiOPoQ.lemma_4_4_algorithm_B
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:59.319846+00:00
-- url     : https://prove2.me/theorems/685e65bf-71a7-4665-9573-7ee6ede410f9
-- title:
--   Lemma 4.4, proof: the algorithm $B$ puts $L$ in i.o.P/poly
-- statement:
--   Let $L$ be decided by $V_\lambda$, let $C_{b,\lambda}$ be a padding, let Obf be any classical PPT algorithm and $A$ any non-uniform classical PPT adversary. If $\lambda\mapsto|p_0(\lambda)-p_1(\lambda)|$ is not negligible and $\gamma$ is bounded by a negligible function, then $L\in$ i.o.P/poly.
--
--   The algorithm $B$ estimates $p_0(\lambda)$, $p_1(\lambda)$ and $q_x(\lambda)$ by fresh obfuscations and runs of $A$ and outputs the $b$ for which $p_b$ is closer to $q_x$. No security of the obfuscator is used here, only that $B$ can run Obf, $A$ and the generators of $V_\lambda$ and $C_{b,\lambda}$.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any finite gate set with designated I, X, CNOT and an adjoint map; reason: no step uses universality; every universal gate set of the required form is an instance
--   - reading: BQP ⊄ i.o.P/poly, with Notation 4.1 choosing L ∈ BQP \ i.o.P/poly and V_λ → for every L ∉ i.o.P/poly decided by uniformly generated V_λ with negligible error and an ancilla output wire; reason: the construction is built from this datum (Notation 4.1, proof of Lemma 4.4); the universal quantifier covers whichever choice is made
--   - generalization: C_{b,λ}: "Pad C_{b,λ} so that it has the required gate count", no specific padding → every family with the printed shape, output wire, channel X^b(·) and polynomial-time construction; reason: specializes to whichever padding is chosen
--   - encoding: PPT and non-uniform algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count, a polynomially bounded advice string, and fixed self-delimiting encodings; reason: the standard model; a machine using at most p coins reads exactly p
--   - generalization: the proof of Lemma 4.4, under its hypotheses, deriving the contradiction L ∈ i.o.P/poly → Obf any classical PPT algorithm (no correctness, no security), no hypothesis L ∉ i.o.P/poly; the conclusion is L ∈ i.o.P/poly; reason: B only runs Obf, A and the generators; with L ∉ i.o.P/poly added it gives the printed contradiction
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), proof of Lemma 4.4, p.19

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_IsObfCorrect
import Definitions.Def_QiOPoQ_IsQiOClassical
import Definitions.Def_QiOPoQ_IOPpoly
import Definitions.Def_QiOPoQ_IsDecider
import Definitions.Def_QiOPoQ_IsPadding
import Definitions.Def_QiOPoQ_IsAdmissibleRounds
import Definitions.Def_QiOPoQ_Dx
set_option autoImplicit false
open QAdvFew.PoQOracle QAlgorithms.Complexity

namespace QiOPoQ

open Classical in
/-- **Proof of Lemma 4.4: the algorithm B.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), proof of Lemma 4.4, p.19: "Now, we give a
classical PPT algorithm B that should be able to solve BQP for infinitely many input lengths λ.
The algorithm works as follows: on input x ∈ {0, 1}^λ, it estimates p_0(λ), p_1(λ), and q_x(λ)
using fresh obfuscations and runs of A, up to sufficiently small inverse polynomial additive
accuracy, and outputs b such that the estimate of q_x(λ) is closer to p_b(λ) than p_{1−b}(λ).
Polynomially many samples suffice by a Chernoff bound. Therefore, B is correct on every input of
length λ, for infinitely many input lengths λ, which means that L ∈ i.o.P/poly."

If a non-uniform classical PPT `A` distinguishes the obfuscations of `C_{0,λ}` and `C_{1,λ}`
with non-negligible advantage `|p_0(λ) − p_1(λ)|`, while `γ(λ)` is negligible, then
`L ∈ i.o.P/poly`. (No security of the obfuscator is used: B only runs `Obf`, the generators of
`V_λ` and `C_{b,λ}`, and `A`.) -/
theorem lemma_4_4_algorithm_B (G : GateSet) (Obf : UPPT) (L : Set Str) (V : ℕ → Circ G)
    (hV : IsDecider G L V) (Cb : Bool → ℕ → Circ G) (hCb : IsPadding V Cb) (A : NUPPT)
    (hgap : ¬ Negligible fun n => |obfAcc Obf A n (Cb false n) - obfAcc Obf A n (Cb true n)|)
    (hγ : ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n (x : Str), x.length = n →
      |obfAcc Obf A n (Dx (V n) x) - obfAcc Obf A n (Cb (decide (x ∈ L)) n)| ≤ μ n) :
    IOPpoly L := by sorry

end QiOPoQ
