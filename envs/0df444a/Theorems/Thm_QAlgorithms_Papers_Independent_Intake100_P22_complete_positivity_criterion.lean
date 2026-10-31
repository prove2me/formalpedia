-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P22_complete_positivity_criterion
-- name    : QAlgorithms.Papers.Independent.Intake100.P22.complete_positivity_criterion
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:47:14.864981+00:00
-- url     : https://prove2.me/theorems/eed47598-ae9b-406b-ac04-fb8be29059c2
-- title:
--   Complete positivity with the zero-prefactor case made explicit
-- statement:
--   Fix a finite number $n\ge0$ of fermionic modes. Let $\mathcal C_{2n}=\operatorname{End}(\mathbb C^{2^n})$ have Hermitian Majorana generators $c_a$ satisfying $c_ac_b+c_bc_a=2\delta_{ab}I$. The symbol map $\omega$ sends each ordered Majorana monomial linearly to the corresponding ordered Grassmann monomial; it is not multiplicative. Gaussian states, operators, and maps have the meanings of Definitions 1–3 of the paper. All maps act on the full complex operator algebra, including its odd sector.
--
--   Let $E$ be a Gaussian map with given skew diagonal blocks $A,D$, arbitrary complex block $B$, and scalar prefactor $C$. Write
--   $$
--   \mathcal M=\begin{pmatrix}A&B\\-B^T&D\end{pmatrix}.
--   $$
--   The complete criterion, including the zero map, is
--   $$
--   E\text{ is completely positive}\quad\Longleftrightarrow\quad
--   C=0\ \text{or}\ \bigl(C\in\mathbb R_{>0},\ \mathcal M\text{ real},\ \mathcal M^T\mathcal M\le I\bigr).
--   $$
--   The inequality is positive-semidefinite matrix order. No trace-preserving or trace-nonincreasing restriction is imposed. This states complete positivity for arbitrary specified kernels.
--
--   **Source correction.** The printed conjunction $C\ge0$ with a real contractive block omits the freedom of block parameters when $C=0$. Every such kernel defines the same zero CP map. The proof takes $C>0$; Lemma 7 explicitly includes zero. The displayed disjunction corrects this case and requires independent moderation.
-- source:
--   Lagrangian representation for fermionic linear optics, arXiv:quant-ph/0404180v2, PDF p. 9, Theorem 2: complete-positivity criterion for Gaussian maps

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P22

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intake100.P22

open QAlgorithms.Papers.Independent.Advance50.P19
  (CARSystem Major monomial wick totalFermionParity)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.9-11, Theorem 2, corrected at zero prefactor. Printed: C>=0 and
real contractive block. Changed: C=0 OR C>0 real with real contractive block.
Reason: C=0 always defines the zero CP map, with arbitrary A,B,D; the proof
implicitly takes C>0, while Lemma 7 explicitly includes the zero map.
The contraction inequality is PSD order. Independent moderation is required. -/
theorem complete_positivity_criterion {n : ℕ} (s : CARSystem n)
    (E : Superop (Qubits n) (Qubits n)) (K : GrassmannKernel n) (hE : HasGrassmannKernel s E K) :
    LinearCompletelyPositive E ↔ K.C = 0 ∨
      (K.C.im = 0 ∧ 0 < K.C.re ∧ RealContraction (kernelBlock K)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P22

end
