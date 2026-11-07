-- Prove2me | Theorems.Thm_QiOPoQ_theorem_4_7_hybrid_steps
-- name    : QiOPoQ.theorem_4_7_hybrid_steps
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:08:22.087167+00:00
-- url     : https://prove2.me/theorems/5615b565-f279-437e-b8f6-85e3492b38cd
-- title:
--   Theorem 4.7, proof: consecutive hybrids are indistinguishable
-- statement:
--   Let Obf have qiO security against classical adversaries, let $L\notin$ i.o.P/poly be decided by $V_\lambda$, let $C_{b,\lambda}$ be a padding, $f$ polynomial-time computable and $t$ admissible. For every non-uniform classical PPT adversary $A$ there is a negligible $\mu$ such that, for all $\lambda$ and all $i<t(\lambda)$,
--
--   $$
--   |p_{2i}(\lambda)-p_{2i+1}(\lambda)|\le\mu(\lambda)\quad\text{and}\quad|p_{2i+1}(\lambda)-p_{2i+2}(\lambda)|\le\mu(\lambda),
--   $$
--
--   where $p_k$ is the winning probability of $A$ in the hybrid $H_k$.
--
--   The reductions compute $y=f(b)$ themselves, so one-wayness of $f$ is not used here, only its efficiency.
--
--   Differences from the source:
--   - generalization: a fixed finite universal gate set containing I, X, CNOT, closed under adjoints → any finite gate set with designated I, X, CNOT and an adjoint map; reason: no step uses universality; every universal gate set of the required form is an instance
--   - reading: BQP ⊄ i.o.P/poly, with Notation 4.1 choosing L ∈ BQP \ i.o.P/poly and V_λ → for every L ∉ i.o.P/poly decided by uniformly generated V_λ with negligible error and an ancilla output wire; reason: the construction is built from this datum (Notation 4.1, proof of Lemma 4.4); the universal quantifier covers whichever choice is made
--   - generalization: C_{b,λ}: "Pad C_{b,λ} so that it has the required gate count", no specific padding → every family with the printed shape, output wire, channel X^b(·) and polynomial-time construction; reason: specializes to whichever padding is chosen
--   - reading: C_BQP: for C of description length λ, ∥C − X^{b_C}(·)∥⋄ ≤ negl(λ) → membership of polynomial-size families, with one negligible function per family; reason: negl(λ) has a meaning only for a family; Definition 3.2 quantifies over polynomial-size families
--   - encoding: PPT and non-uniform algorithms → a deterministic TM2 polynomial-time map with an explicit polynomial coin count, a polynomially bounded advice string, and fixed self-delimiting encodings; reason: the standard model; a machine using at most p coins reads exactly p
--   - reading: |p_{2i} − p_{2i+1}| ≤ negl(λ) for all i = 0, …, t − 1, and likewise |p_{2j+1} − p_{2j+2}| → one negligible μ for all i < t(λ); reason: the triangle inequality over the 2t hybrids uses the bound uniformly in i; the reduction takes the worst i as advice
--   - generalization: the hypotheses of Theorem 4.7 (a correct and qiO-secure scheme) and a one-way f → qiO security only (no correctness), and f only polynomial-time computable (not one-way); reason: the reductions to Lemma 4.4 compute y := f(b) and use only security; every instance of Theorem 4.7 is covered
--   - reading: t := t(λ) with t ≤ poly(λ), t ≥ Ω(λ) (Notation 4.1) → t computable from 1^λ in polynomial time, t(λ) ≤ p(λ) for a polynomial p, and ∃ c > 0, ∃ N, ∀ λ ≥ N, c·λ ≤ t(λ) (IsAdmissibleRounds); reason: Ω(λ) in its usual sense; computability is implied because Challenge and Verify are classical polynomial-time (Definition 3.3) and must compute t
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), proof of Theorem 4.7, p.22

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QiOPoQ_IsObfCorrect
import Definitions.Def_QiOPoQ_IsQiOClassical
import Definitions.Def_QiOPoQ_IOPpoly
import Definitions.Def_QiOPoQ_IsDecider
import Definitions.Def_QiOPoQ_IsPadding
import Definitions.Def_QiOPoQ_IsAdmissibleRounds
import Definitions.Def_QiOPoQ_hybProb
set_option autoImplicit false
open QAdvFew.PoQOracle QAlgorithms.Complexity

namespace QiOPoQ

/-- **Proof of Theorem 4.7: consecutive hybrids are indistinguishable.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), proof of
Theorem 4.7, p.22: "We claim that |p_{2i} − p_{2i+1}| ≤ negl(λ) for all i = 0, 1, . . . , t − 1.
Suppose for contradiction there is a PPT distinguisher. Then, we have a distinguisher that
contradicts Lemma 4.4, via the following reduction: given input Ĉ, sample random b ∈ {0, 1}^t,
compute y := f(b), and compute the challenge circuits Ĉ_j for j ≠ i + 1 to be consistent with
both hybrids H_{2i} and H_{2i+1}. … A direct reduction and application of Lemma 4.4 also shows
that |p_{2j+1} − p_{2j+2}| ≤ negl(λ)."

**Formalization Note.** One negligible `μ` bounds every step `i < t(λ)` (the triangle inequality
over the `2t` hybrids, "since we have only polynomially many hybrids", needs the bound uniformly
in `i`). The reductions compute `y = f(b)`, so `f` is polynomial-time; one-wayness is not used. -/
theorem theorem_4_7_hybrid_steps (G : GateSet) (Obf : UPPT) (hqiO : IsQiOClassical G Obf)
    (L : Set Str) (V : ℕ → Circ G) (hV : IsDecider G L V) (hL : ¬ IOPpoly L)
    (Cb : Bool → ℕ → Circ G) (hCb : IsPadding V Cb) (f : Str → Str) (hf : PolyTimeComputable f)
    (t : ℕ → ℕ) (ht : IsAdmissibleRounds t) (A : NUPPT) :
    ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ n, ∀ i < t n,
      |hybProb Obf Cb f t A n (2 * i) - hybProb Obf Cb f t A n (2 * i + 1)| ≤ μ n ∧
      |hybProb Obf Cb f t A n (2 * i + 1) - hybProb Obf Cb f t A n (2 * i + 2)| ≤ μ n := by sorry

end QiOPoQ
