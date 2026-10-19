-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P34_invariant_comb_block_form
-- name    : QAlgorithms.Papers.Independent.Information100.P34.invariant_comb_block_form
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:56:21.311323+00:00
-- url     : https://prove2.me/theorems/781e975a-bfa1-4ed9-8452-277269528803
-- title:
--   Lemma 22: block form of twirl-invariant deterministic superchannels
-- statement:
--   Let the outer wires $0,3$ have the same positive dimension $d$, and let internal wires $1,2$ have positive dimensions $a,b$. Under the standing convention, the two internal wires are not both trivial. Let $J$ be an arbitrary operator on wires $0,1,2,3$ and let $\mathcal T^{03}$ be the actual average of the Fourier–Weyl conjugations on the outer wires. Then
--
--   $$J\in\mathrm{Comb}_1\ \text{and}\ (\mathrm{id}^{12}\otimes\mathcal T^{03})(J)=J$$
--
--   if and only if there exist positive semidefinite operators $Y_{k,l}$ on wires $1,2$ and $M$ on wire $1$ such that
--
--   $$J=\sum_{k,l}Y_{k,l}^{12}\otimes\Pi_{k,l}^{03},\qquad\sum_{k,l}Y_{k,l}=M\otimes I_2,\qquad\operatorname{Tr}M=d.$$
--
--   Tensor factors in the displayed decomposition are permuted into wire order $0,1,2,3$. The reverse implication includes deterministic comb membership.
-- source:
--   The Structure of Higher-Order Quantum Resources with an Application to Coherence, arXiv:2609.40186v1, PDF p. 37, Lemma 22

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

/-- Lemma 22, Eqs.(C109-C110), PDF pp.37-38. The converse establishes
comb membership; M has trace d. The slot has at least one nontrivial wire. -/
theorem invariant_comb_block_form {d a b : ℕ} [NeZero d]
    (ha : 0 < a) (hb : 0 < b) (hslot : 1 < a ∨ 1 < b)
    (J : Matrix ((ZMod d × Fin a) × (Fin b × ZMod d))
      ((ZMod d × Fin a) × (Fin b × ZMod d)) ℂ) :
    (CombOne J ∧ twirlOuter J = J) ↔
    ∃ Y : ZMod d → ZMod d → Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ,
      (∀ k l, (Y k l).PosSemidef) ∧
      J = ∑ k : ZMod d, ∑ l : ZMod d, blockOuter (Y k l) (jointProjector k l) ∧
      ∃ M : Matrix (Fin a) (Fin a) ℂ, M.PosSemidef ∧ M.trace = (d : ℂ) ∧
        (∑ k : ZMod d, ∑ l : ZMod d, Y k l) = Matrix.kronecker M 1 := by sorry

end QAlgorithms.Papers.Independent.Information100.P34

end
