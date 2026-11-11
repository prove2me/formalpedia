-- Prove2me | Theorems.Thm_QNatProofs_par25_lemma_6_3
-- name    : QNatProofs.par25_lemma_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:50.667025+00:00
-- url     : https://prove2.me/theorems/16c400e0-73ae-47de-a8f5-b9e6c12ddb05
-- title:
--   [Par25, Lemma 6.3] (as used on p.33) — depth-$d$ TC$^0$ in $A_{4d}CQ$
-- statement:
--   For every depth $d\ge1$ there are a QNC$^0$ depth $D$ and a polynomial $p$ such that every threshold circuit $\Phi$ of depth at most $d$ with $n$ inputs and $R$ outputs has a nonclean coherent evaluator in $A_{4d}CQ$:
--   $$
--   U|x\rangle|0^R\rangle|0^w\rangle=|x\rangle|\Phi(x)\rangle|\mathrm{junk}_x\rangle\qquad\text{for every }x\in\{0,1\}^n,
--   $$
--   with at most $p(n+R+\mathrm{size}(\Phi))$ gates and $w\le p(n+R+\mathrm{size}(\Phi))$ workspace wires.
--
--   The paper uses this cited result in the proof of Corollary 4.6.2: "By the nonclean simulation of depth-$d_F$ TC$^0$ circuits in $A_{4d_F}CQ$ from [Par25, Lemma 6.3], each $F_k$ therefore has a polynomial-size coherent evaluator in $A_{4d_F}CQ$."
--
--   Differences from the source:
--   - reading: A_kCQ / MH_k (defined in [Par25], not in the paper) → MHLevel k D: C₀Q₁C₁⋯Q_kC_k with Clifford segments C_i of any length and one- and two-qubit unitary segments Q_i of depth ≤ D; reason: the paper's own level counts (p.25: [Cliff][A₄][Cliff][A₄][Cliff] ⊆ A₈; p.40: A₁ = Clifford then QNC⁰) fix this form; A_kCQ ⊆ MH_k on p.22
--   - reading: polynomial-size coherent evaluator in A_{4d_F}CQ, [Par25, Lemma 6.3] → ∀ d ≥ 1, ∃ D, ∃ polynomial p, ∀ threshold circuit Φ of depth ≤ d: an evaluator in MHLevel (4d) D with size and workspace ≤ p(n + R + size Φ); reason: the statement as this paper uses it; [Par25] itself was not consulted, and its hypotheses are not reproduced
--   - encoding: TC⁰ circuits → ThrCircuit: unbounded fan-in threshold gates with repeated literals as weights; reason: standard TC⁰ with polynomially bounded weights
-- source:
--   Li, Parham, Natural proofs for quantum state preparation lower bounds, arXiv:2610.06826 (held copy sha256 b604fa11…), proof of Corollary 4.6.2, p.33, citing N. Parham, Quantum circuit lower bounds in the magic hierarchy, arXiv:2504.19966, Lemma 6.3 (not consulted)

import Mathlib
import Definitions.Def_QNatProofs_MHLevel
import Definitions.Def_QNatProofs_ThrCircuit

set_option autoImplicit false

namespace QNatProofs

open QAlgorithms Polynomial

/-- **[Par25, Lemma 6.3], as used in the proof of Corollary 4.6.2** (Li, Parham, *Natural proofs for
quantum state preparation lower bounds*, arXiv:2610.06826 (held copy sha256 b604fa11…), p.33,
citing N. Parham, *Quantum circuit lower bounds in the magic hierarchy*, arXiv:2504.19966,
Lemma 6.3): "By the nonclean simulation of depth-`d_F` TC⁰ circuits in `A_{4d_F}CQ` from [Par25,
Lemma 6.3], each `F_k` therefore has a polynomial-size coherent evaluator in `A_{4d_F}CQ`."

For every depth `d ≥ 1` there are a QNC⁰ depth `D` and a polynomial `p` such that every threshold
circuit `Φ` of depth at most `d` with `n` inputs and `R` outputs has a nonclean coherent evaluator
`|x⟩|0^R⟩|0^w⟩ ↦ |x⟩|Φ(x)⟩|junk_x⟩` in `A_{4d}CQ` with at most `p(n + R + size(Φ))` gates and
workspace wires.

**Formalization Note** This is the statement this paper uses; [Par25] itself was not consulted.
`A_kCQ` is `MHLevel k D`; threshold circuits are `ThrCircuit` (unbounded fan-in majority-type
gates with repeated literals as weights). -/
theorem par25_lemma_6_3 (d : ℕ) (hd : 1 ≤ d) : ∃ (D : ℕ) (p : ℕ[X]),
    ∀ (n R : ℕ) (Φ : ThrCircuit n R), Φ.depth ≤ d →
    ∃ (w : ℕ) (U : Circuit allGates (n + (R + w))), U ∈ MHLevel (4 * d) D _ ∧
      IsNoncleanEval (r := R) (w := w) U.unitary Φ.eval ∧
      U.size ≤ p.eval (n + R + Φ.size) ∧ w ≤ p.eval (n + R + Φ.size) := by sorry

end QNatProofs
