-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_proposition_11
-- name    : TDHamSim.QueryOptimal.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:22:46.101938+00:00
-- url     : https://prove2.me/theorems/0d063f86-807c-4d14-bc15-c524ba92f412
-- title:
--   Proposition 11 — gate count for SELECT
-- statement:
--   There is an absolute constant $C>0$ such that, for $\alpha T>0$, integer $q\ge\max\{1,\alpha T\}$ and $J=2^m\ge\max\{2,q\}$, fixed standard circuits implement SELECT, SELECT$^\dagger$ and $V$. SELECT and SELECT$^\dagger$ each use exactly $4q$ controlled HAM-T queries, and each of the three circuits uses at most
--
--   $$Cq(a+m+\log(q+1))\quad\text{and}\quad Cq(a+m+1)$$
--
--   additional gates. Temporary work qubits return to zero. Moreover,
--
--   $$(\langle0|\otimes I)V(|0\rangle\otimes I)=\widetilde U/2,$$
--
--   and $V$ is unitary. The circuits are chosen before the Hermitian unitary oracle blocks.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - encoding: an unspecified unitary completion of a uniform state preparation F_N → the explicit real Householder completion of that uniform column; reason: P_N depends only on the uniform column; this fixes a source choice without changing the encoded operator
--   - encoding: O(·) resource bounds → one positive absolute real constant chosen before all parameters; reason: a single constant can dominate the finitely many universal constants, with logarithm-base factors absorbed
--   - generalization: the source HAM-T blocks encoding sampled Hamiltonians → every family of Hermitian unitary blocks; reason: the implementation and block-encoding identities depend only on those blocks and the update weight
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Proposition 11 — gate count for SELECT, p.31. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_LCU

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- Proposition 11, p.31: SELECT, its inverse, V, and normalization-two block encoding. -/
theorem proposition_11 :
    ∃ C : ℝ, 0 < C ∧ ∀ (m a n q : ℕ) (α T : ℝ),
      0 < α → 0 < T → 1 ≤ m → 1 ≤ q → α*T ≤ q → q ≤ 2^m →
      let b := reuseWidth q
      ∃ k : ℕ, ∃ cs ct cv : ConstDepthUnitary.OCircuit (Wires (2*b+(1+m+a+n)) k) (1+m+a+n),
        cs.IsStandard ∧ ct.IsStandard ∧ cv.IsStandard ∧
        cs.queries = 4*q ∧ ct.queries = 4*q ∧
        (∀ c ∈ [cs, ct, cv], (extraGates c : ℝ) ≤ C*q*(a+m+Real.log (q+1)) ∧
          (extraGates c : ℝ) ≤ C*q*(a+m+1)) ∧
        ∀ O : Fin (2^m) → Mat (Bits a × Bits n),
          (∀ j, (O j).IsHermitian ∧ IsUnitary (O j)) →
          Implements cs (controlledHAMT O) (selectBits q b (stepWeight α T (2^m)) O) ∧
          Implements ct (controlledHAMT O) (selectBits q b (stepWeight α T (2^m)) O).conjTranspose ∧
          Implements cv (controlledHAMT O) (vBits q b (stepWeight α T (2^m)) O) ∧
          QAlgorithms.IsBlockEncoding (auxZero b m a) (lcuV q b (stepWeight α T (2^m)) O) 2 0
            (uTilde q b (stepWeight α T (2^m)) O) := by sorry

end TDHamSim.QueryOptimal
