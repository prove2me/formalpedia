-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P31_binaryBistochasticCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P31.binaryBistochasticCapacity
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:31:17.969982+00:00
-- url     : https://prove2.me/theorems/c035de2c-1790-49c7-ad22-a5f89d2b6f26
-- title:
--   Binary bistochastic capacity and the conditional additivity implication
-- statement:
--   Let $\Phi$ be a binary bistochastic channel: a completely positive trace-preserving endomorphism of $2\times2$ complex matrices satisfying $\Phi(I)=I$. Let $C$ denote the one-step finite-ensemble Holevo maximum and $\nu_H$ minimum output entropy, both in natural units. Then
--   $$
--   C(\Phi)=\log2-\nu_H(\Phi).
--   $$
--   Moreover, for every $n\ge1$ and every tuple of binary bistochastic channels $(\Phi_i)_{i=1}^n$,
--   $$
--   \nu_H\!\left(\bigotimes_i\Phi_i\right)=\sum_i\nu_H(\Phi_i)
--   \quad\Longrightarrow\quad
--   C\!\left(\bigotimes_i\Phi_i\right)=\sum_i C(\Phi_i).
--   $$
--   Each output optimization ranges over all density inputs, and $C$ is not a regularized capacity. The second clause transfers an entropy-additivity hypothesis to one-step capacity additivity; it is not an unconditional proof of either conjecture.
-- source:
--   On some additivity problems in quantum information theory, arXiv:math-ph/0003002v2, PDF p. 9, §5, Lemma (18) and its second clause

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P31

noncomputable section

open Filter Asymptotics

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P31

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Gap48.P03 (holevoQuantity)

open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

open QAlgorithms.Papers.Independent.Dependency50.P44 (tensorChannels)

/-- PDF p.9, Lemma (18), BOTH clauses: binary bistochastic formula, and the
conditional implication from entropy additivity to one-step capacity additivity. -/
theorem binaryBistochasticCapacity (Phi : Superop (Fin 2) (Fin 2))
    (hPhi : IsChannel Phi) (hunital : Phi 1 = 1) :
    holevoQuantity Phi = Real.log 2 - nuH Phi ∧
    ∀ (n : ℕ) (_hn : 0 < n) (Psi : Fin n → Superop (Fin 2) (Fin 2)),
      (∀ i, IsChannel (Psi i) ∧ Psi i 1 = 1) →
      nuH (piSuperop Psi) = ∑ i, nuH (Psi i) →
      holevoQuantity (piSuperop Psi) = ∑ i, holevoQuantity (Psi i) := by sorry

end QAlgorithms.Papers.Independent.Support50.P31

end
