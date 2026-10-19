-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P39_shannonCollisionReversal
-- name    : QAlgorithms.Papers.Independent.Information100.P39.shannonCollisionReversal
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:24:21.496184+00:00
-- url     : https://prove2.me/theorems/a8cfd206-86c8-4d5e-80bc-ba8bdf193840
-- title:
--   Appendix A.2: failure of the Shannon–collision hierarchy
-- statement:
--   Take the two-qubit code stabilized by $X_1X_2$, with logical $\overline X=X_1$ and $\overline Z=Z_1Z_2$. Use normalized codewords $(|00\rangle+|11\rangle)/\sqrt2$ and $(|01\rangle+|10\rangle)/\sqrt2$. Leave qubit two noiseless and apply $\nu_A=(1,3,6,6)/16$ to qubit one. With $Z_1$ as representative for the nontrivial syndrome, the actual joint syndrome/logical law is
--
--   $$P=\frac1{16}\begin{pmatrix}1&3&0&0\\6&6&0&0\end{pmatrix}.$$
--
--   For the normalized noisy encoded Choi state, the deficit equals $H_r(P)-H_r(P_S)$ at every positive integer order and infinity. In particular, writing $h_{\rm bin}(x)=-x\log x-(1-x)\log(1-x)$,
--
--   $$\Delta_1=\tfrac14h_{\rm bin}(\tfrac14)+\tfrac34\log2
--   <\Delta_2=\log\tfrac{80}{41},\qquad I_c^{(1)}>I_c^{(2)}.$$
--
--   The Fourier triple of $\nu_A$ is $(-1/2,-1/8,-1/8)$, excluding an independent-event representation of the full noise. This is an exact Shannon-to-collision reversal; the source's numerical chain through order 100 is not included as a theorem.
-- source:
--   Hierarchy of Rényi Coherent Information in Stabilizer Codes, arXiv:2609.11930v1, PDF p. 9, Appendix A.2: failure of the Shannon–collision hierarchy

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P39

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- Appendix A.2, PDF p.9, Eqs.(S6)–(S8): actual-code Shannon/collision
reversal, its joint-law entropy identity, and exact deficits. No numerical
chain through order 100 is asserted. -/
theorem shannonCollisionReversal :
    ∃ hnu : Learning.IsDistribution shannonCounterexampleNoise,
      IsEncoderFor (![pauliOps (fun _ : Fin 2 => Stabilizer.Pauli.X)])
        shannonCounterexampleEncoder ∧
      Learning.IsDistribution shannonCounterexampleJoint ∧
      (∀ s l, effectProb (shannonBellSector s l)
        (noisyChoi shannonCounterexampleEncoder shannonCounterexampleNoise hnu) =
        shannonCounterexampleJoint (s,l)) ∧
      SparsePauliNoise.eigenvalueWHT (pauliVector (![1/16,3/16,6/16,6/16])) labelX = -1/2 ∧
      SparsePauliNoise.eigenvalueWHT (pauliVector (![1/16,3/16,6/16,6/16])) labelY = -1/8 ∧
      SparsePauliNoise.eigenvalueWHT (pauliVector (![1/16,3/16,6/16,6/16])) labelZ = -1/8 ∧
      ¬ HasIndependentEvents shannonCounterexampleNoise ∧
      (∀ r : Order, 1 ≤ r →
        quantumDeficit shannonCounterexampleEncoder shannonCounterexampleNoise hnu r =
        entropy r shannonCounterexampleJoint -
          entropy r (pushLaw shannonCounterexampleJoint Prod.fst)) ∧
      quantumDeficit shannonCounterexampleEncoder shannonCounterexampleNoise hnu 1 =
        (1/4)*Real.binEntropy (1/4) + (3/4)*Real.log 2 ∧
      quantumDeficit shannonCounterexampleEncoder shannonCounterexampleNoise hnu 2 =
        Real.log (80/41) ∧
      quantumDeficit shannonCounterexampleEncoder shannonCounterexampleNoise hnu 1 <
        quantumDeficit shannonCounterexampleEncoder shannonCounterexampleNoise hnu 2 ∧
      coherentInformation 2 (noisyChoi shannonCounterexampleEncoder shannonCounterexampleNoise hnu) <
        coherentInformation 1 (noisyChoi shannonCounterexampleEncoder shannonCounterexampleNoise hnu) := by sorry

end QAlgorithms.Papers.Independent.Information100.P39

end
