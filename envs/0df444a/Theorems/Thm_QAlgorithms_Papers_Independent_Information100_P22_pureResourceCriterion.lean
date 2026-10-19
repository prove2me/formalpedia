-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_pureResourceCriterion
-- name    : QAlgorithms.Papers.Independent.Information100.P22.pureResourceCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:47:41.57599+00:00
-- url     : https://prove2.me/theorems/32d0b371-810e-471d-bb2a-b22cf2828bc6
-- title:
--   Theorem 1 (seed): Exact fixed-encoder pure-resource criterion
-- statement:
--   Let $m\ge2$, $k\ge1$, $\nu=mk$, and let $P\ne Q$ be ordered Pauli axes. Fix the source's sector encoder $U$ and a normalized pure resource $R$ on $S N$, with $\nu$ qubits on each side. Write $\rho_S=\operatorname{Tr}_N|R\rangle\langle R|$, $R_0=iPQ$, and $T(c)=\bigotimes_{j,i}R_0^{c_j}$ for $c\in\{0,1\}^k$. With unrestricted fixed CPTP decoders receiving exactly $S_iN$,
--   $$\text{every }S_iN\text{ exactly recovers the entire input}\iff\begin{cases}\rho_S=I/2^\nu,&m\text{ even},\\ \rho_S=2^{-\nu}\sum_c\alpha_cT(c),\quad\alpha_0=1,\ \alpha_c\in\mathbb R,\ \rho_S\succeq0,&m\text{ odd}.\end{cases}$$
--   Whenever the criterion holds, every individual signal channel is $X\mapsto\operatorname{Tr}(X)I/2^k$. This classifies the exact resources for the fixed encoder, including reference-entangled inputs.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 4, Theorem 1 (seed): Exact fixed-encoder pure-resource criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Theorem 1, PDF p.4, proof pp.21–23. -/
theorem pureResourceCriterion (m k : ℕ) (hm : 2 ≤ m) (hk : 1 ≤ k)
    (P Q : Axis) (hPQ : P ≠ Q)
    (R : EuclideanSpace ℂ (Signals m k × Signals m k)) (hR : IsState R) :
    (AllRecoverable R (twoPauliEncoder m k P Q) ↔ ResourceCriterion P Q (rhoS R)) ∧
    (ResourceCriterion P Q (rhoS R) → UniformlyConcealed R (twoPauliEncoder m k P Q)) := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
