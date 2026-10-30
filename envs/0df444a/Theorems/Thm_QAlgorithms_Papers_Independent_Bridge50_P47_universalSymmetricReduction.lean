-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_universalSymmetricReduction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.universalSymmetricReduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:53:10.306698+00:00
-- url     : https://prove2.me/theorems/307661ad-ec32-414a-90a8-8b65491f797c
-- title:
--   Section VII: universal symmetric channels suffice
-- statement:
--   For a nonzero finite system $E\cong\mathbb C^d$, let $\mathcal S_d:\mathcal L(\operatorname{Sym}^2(E))\to\mathcal L(E)$ be the channel whose Stinespring isometry is the actual subspace inclusion $\operatorname{Sym}^2(E)\hookrightarrow E\otimes E$. In coordinates, its orthonormal input basis consists of $|ii\rangle$ and $(|ij\rangle+|ji\rangle)/\sqrt2$ for $i<j$. A strong converse for these universal channels suffices for every finite degradable channel. In particular, for fixed nonzero finite input and output systems $A,B$,
--
--   $$
--   \operatorname{SC}(\mathcal S_{2(\dim A)(\dim B)})\ \Longrightarrow\ \operatorname{SC}(\mathcal N)\quad\text{for every degradable }\mathcal N:\mathcal L(A)\to\mathcal L(B).
--   $$
--
--   Here $\operatorname{SC}$ denotes the unassisted quantum strong converse, expressed through all fixed purified-error entanglement-generation rates below error one. Consequently, if $\operatorname{SC}(\mathcal S_d)$ holds for every positive integer $d$, it holds for all finite degradable channels. This is a conditional sufficiency statement, including the fixed-dimension refinement.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 12, Section VII: universal symmetric channels suffice

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P47

open QAlgorithms.Papers.Independent.Information100

variable {A B E F R I O : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

variable [Fintype O] [DecidableEq O]

/-- Section VII universal-channel Remark, PDF p.12 (summary p.13): a
conditional reduction, including the dimension 2 dim(A) dim(B) refinement. -/
theorem universalSymmetricReduction [Nonempty A] [Nonempty B] [Nonempty E] :
    ((∀ d : ℕ, 0 < d → StrongConverse (universalSymmetricDilation d)) →
      ∀ U : Matrix (B × E) A ℂ, P67.IsDegradable U → StrongConverse U) ∧
    (StrongConverse (universalSymmetricDilation (2 * Fintype.card A * Fintype.card B)) →
      ∀ U : Matrix (B × E) A ℂ, P67.IsDegradable U → StrongConverse U) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
