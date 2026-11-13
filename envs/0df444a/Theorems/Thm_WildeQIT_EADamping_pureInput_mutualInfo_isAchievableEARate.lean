-- Prove2me | Theorems.Thm_WildeQIT_EADamping_pureInput_mutualInfo_isAchievableEARate
-- name    : WildeQIT.EADamping.pureInput_mutualInfo_isAchievableEARate
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T04:54:00.74982+00:00
-- url     : https://prove2.me/theorems/e73b06dc-5408-4afc-b392-dd60eb7a6e25
-- title:
--   Direct part of the entanglement-assisted classical capacity theorem: $I(A;B)_\rho$ is achievable
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel between finite-dimensional systems and let $\varphi_{AA'}$ be any pure bipartite input state, with a reference system $A$ of any finite dimension. Then the quantum mutual information
--
--   $$I(A;B)_\rho, \qquad \rho_{AB} = (\mathrm{id}_A\otimes\mathcal N_{A'\to B})(\varphi_{AA'}),$$
--
--   is an achievable rate of entanglement-assisted classical communication over $\mathcal N$.
--
--   Role: this is the direct (achievability) half of the entanglement-assisted capacity theorem; in the parent it shows that the channel mutual information of the amplitude damping channel, which is attained by a pure input, is itself achievable, so it is the least upper bound of the achievable rates.
-- source:
--   Mark M. Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, https://arxiv.org/abs/1106.1445, Theorem 21.4.1 (Bennett-Shor-Smolin-Thapliyal), p. 593; direct coding theorem in Section 21.4, pp. 593-600

import Mathlib
import Definitions.Def_WildeQIT_EADamping_channelMutualInfo
import Definitions.Def_WildeQIT_EADamping_IsAchievableEARate
open WildeQIT

namespace WildeQIT.EADamping

theorem pureInput_mutualInfo_isAchievableEARate {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (N : QChannel a b) (φ : WildeQIT.Degradable.PureInput a) :
    IsAchievableEARate N
      (DattaDiscord.mutualInfo (idTensorApply N (QAlgorithms.pureDensity φ.ψ))) := by sorry

end WildeQIT.EADamping
