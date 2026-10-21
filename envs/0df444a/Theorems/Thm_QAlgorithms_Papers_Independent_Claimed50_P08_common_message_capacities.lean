-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P08_common_message_capacities
-- name    : QAlgorithms.Papers.Independent.Claimed50.P08.common_message_capacities
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:19:19.854975+00:00
-- url     : https://prove2.me/theorems/14936b2c-85c0-42af-a8a2-c1719c441b37
-- title:
--   Remark 7: all three exact common-message capacity regions
-- statement:
--   For a finite-dimensional Hadamard broadcast channel, augment each task in Theorems 2, 4 and 6 by an independent uniform common classical message of rate $R_{BC}$ that both receivers must decode. Charlie still has a private classical message of rate $R_C$; Bob's private task is classical, quantum or Bob-only assisted classical communication, respectively. All three rates are nonnegative, there is no secrecy requirement, and no assistance with Charlie. Use actual arbitrary-block common-message codes, including both correct common copies in the joint success criterion. For the quantum task the joint half trace-norm target contains the correct classical copies and the maximally entangled reference/output state. In every model capacity is the Euclidean closure of achievable rates with arbitrary positive error/slack tolerances and all sufficiently large positive blocklengths.
--
--   The following three operational region equalities hold simultaneously:
--
--   $$
--   \begin{aligned}
--   \mathcal C_{\rm cl}^{\rm common}&=\{(R_B,R_C,R_{BC})\ge0:\ \exists\theta\text{ as in (21)},\ R_B\le I(Z;B\mid W)_\theta,\ R_{BC}+R_C\le I(W;C)_\theta\},\\
--   \mathcal C_{\rm cq}^{\rm common}&=\{(Q_B,R_C,R_{BC})\ge0:\ \exists\theta\text{ as in (73)},\ Q_B\le I(R\rangle BW)_\theta,\ R_{BC}+R_C\le I(W;C)_\theta\},\\
--   \mathcal C_{\rm pea}^{\rm common}&=\{(R_B,R_C,R_{BC})\ge0:\ \exists\theta\text{ as in (103)},\ R_B\le I(R;B\mid W)_\theta,\ R_{BC}+R_C\le I(W;C)_\theta\}.
--   \end{aligned}
--   $$
--
--   In the first line, $W,Z$ are arbitrary finite nonempty alphabets, $p_{WZ}$ is a joint distribution and the input states $\varphi_A^z$ are pure and indexed by $z$ only. In the other lines, $W,R$ have arbitrary positive finite dimensions, $p_W$ is a distribution and $\varphi_{RA}^w$ are pure. In every line $\theta$ is the actual output of the same Hadamard channel on the indicated classical ensemble, and both bounds use the same witness. All information quantities are in bits, with coherent information only in the quantum line. These equalities state the simultaneous common-message extension, leaving Bob's bound unchanged and imposing no additional closure on the existential regions.
-- source:
--   Hadamard quantum broadcast channels, arXiv:1611.07651v3, PDF p. 16, Remark 7: simultaneous common-message extensions of Theorems 2, 4, and 6

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P08

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P58 (Distribution)

open QAlgorithms.Papers.Independent.Information100.P67 (groupedChannelPower mapFirst)

/-- PDF p.16, Remark 7: all THREE exact common-message extensions, using
independent uniform common messages decoded by both receivers. Only Charlie's
single-letter bound becomes R_BC+R_C; Bob's private bound is unchanged.
There is no secrecy or assistance with Charlie. -/
theorem common_message_capacities {a b c : ℕ} (H : HadamardData a b c) :
    (commonCapacity .classical (hadamardChannel H) =
      {rates | classicalRegion (hadamardChannel H) (rates 0, rates 1) (rates 2)}) ∧
    (commonCapacity .classicalQuantum (hadamardChannel H) =
      {rates | classicalQuantumRegion (hadamardChannel H) (rates 0, rates 1) (rates 2)}) ∧
    (commonCapacity .partiallyAssisted (hadamardChannel H) =
      {rates | partiallyAssistedRegion (hadamardChannel H) (rates 0, rates 1) (rates 2)}) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P08

end
