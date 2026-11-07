-- Prove2me | Theorems.Thm_QiOPoQ_lemma_4_4_gamma
-- name    : QiOPoQ.lemma_4_4_gamma
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:07:40.356966+00:00
-- url     : https://prove2.me/theorems/c78ab140-1587-4e57-b983-a6ae9b6c9a42
-- title:
--   Lemma 4.4, proof, eq. (4): $\gamma(\lambda)\le\mathrm{negl}(\lambda)$
-- statement:
--   Let Obf have qiO security against classical adversaries, $L$ be decided by $V_\lambda$, and $C_{b,\lambda}$ be a padding. For a non-uniform classical PPT adversary $A$ write
--
--   $$
--   p_b(\lambda):=\Pr[A(1^\lambda,\mathrm{qiO}(1^\lambda,C_{b,\lambda}))=1],\qquad q_x(\lambda):=\Pr[A(1^\lambda,\mathrm{qiO}(1^\lambda,D_x))=1].
--   $$
--
--   Then $\gamma(\lambda):=\max_{x\in\{0,1\}^\lambda}|q_x(\lambda)-p_{L(x)}(\lambda)|$ is bounded by a negligible function: there is a negligible $\mu$ with $|q_x(\lambda)-p_{L(x)}(\lambda)|\le\mu(\lambda)$ for all $\lambda$ and $x\in\{0,1\}^\lambda$.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any finite gate set with designated I, X, CNOT and an adjoint map; reason: no step uses universality; every universal gate set of the required form is an instance
--   - reading: BQP ⊄ i.o.P/poly, with Notation 4.1 choosing L ∈ BQP \ i.o.P/poly and V_λ → for every L ∉ i.o.P/poly decided by uniformly generated V_λ with negligible error and an ancilla output wire; reason: the construction is built from this datum (Notation 4.1, proof of Lemma 4.4); the universal quantifier covers whichever choice is made
--   - generalization: C_{b,λ}: "Pad C_{b,λ} so that it has the required gate count", no specific padding → every family with the printed shape, output wire, channel X^b(·) and polynomial-time construction; reason: specializes to whichever padding is chosen
--   - reading: C_BQP: for C of description length λ, ∥C − X^{b_C}(·)∥⋄ ≤ negl(λ) → membership of polynomial-size families, with one negligible function per family; reason: negl(λ) has a meaning only for a family; Definition 3.2 quantifies over polynomial-size families
--   - encoding: PPT and non-uniform algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count, a polynomially bounded advice string, and fixed self-delimiting encodings; reason: the standard model; a machine using at most p coins reads exactly p
--   - encoding: ∥·∥⋄, normalization not fixed by the paper → supremum over pure states with a same-size reference, no factor ½; reason: a constant factor does not affect ≤ negl(λ)
--   - generalization: the hypotheses of Lemma 4.4 (a correct and secure qiO scheme, L ∉ i.o.P/poly) → qiO security, the decider V_λ and the padding only; neither correctness of Obf nor L ∉ i.o.P/poly is assumed; reason: the γ claim uses only qiO security on the families D_{x_λ}, C_{L(x_λ),λ}; it specializes to the proof context
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), proof of Lemma 4.4, p.19, eq. (4)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_IsObfCorrect
import Definitions.Def_QiOPoQ_IsQiOClassical
import Definitions.Def_QiOPoQ_IsDecider
import Definitions.Def_QiOPoQ_IsPadding
import Definitions.Def_QiOPoQ_IsAdmissibleRounds
import Definitions.Def_QiOPoQ_Dx
set_option autoImplicit false
open QAdvFew.PoQOracle QAlgorithms.Complexity

namespace QiOPoQ

open Classical in
/-- **Proof of Lemma 4.4: the claim γ(λ) ≤ negl(λ).** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), proof of Lemma 4.4, p.19:
"p_b(λ) := Pr[A(1^λ, qiO(1^λ, C_{b,λ})) = 1] and q_x(λ) := Pr[A(1^λ, qiO(1^λ, D_x)) = 1] …
Further define γ(λ) := max_{x∈{0,1}^λ} |q_x(λ) − p_{L(x)}(λ)| (4). We claim that γ(λ) ≤ negl(λ).
Indeed, otherwise one could select a maximizing x_λ on infinitely many lengths and obtain two
same-shape, negligibly close circuit ensembles that A distinguishes, contradicting the security
of qiO."

For every non-uniform classical PPT `A` there is a negligible `μ` with
`|q_x(λ) − p_{L(x)}(λ)| ≤ μ(λ)` for all `λ` and all `x ∈ {0,1}^λ` (equivalently `γ ≤ μ`). -/
theorem lemma_4_4_gamma (G : GateSet) (Obf : UPPT) (hqiO : IsQiOClassical G Obf) (L : Set Str)
    (V : ℕ → Circ G) (hV : IsDecider G L V) (Cb : Bool → ℕ → Circ G) (hCb : IsPadding V Cb)
    (A : NUPPT) :
    ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n (x : Str), x.length = n →
      |obfAcc Obf A n (Dx (V n) x) - obfAcc Obf A n (Cb (decide (x ∈ L)) n)| ≤ μ n := by sorry

end QiOPoQ
