-- Prove2me | Theorems.Thm_WildeQIT_EADamping_isAchievableEARate_le_channelMutualInfo
-- name    : WildeQIT.EADamping.isAchievableEARate_le_channelMutualInfo
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T04:51:44.840485+00:00
-- url     : https://prove2.me/theorems/793cca3e-8f6d-489b-9585-d273f46c39c5
-- title:
--   Converse of the entanglement-assisted classical capacity theorem: $C \le I(\mathcal N)$
-- statement:
--   Let $\mathcal N_{A'\to B}$ be a quantum channel with a nonempty finite-dimensional input space. If $C$ is an achievable rate of entanglement-assisted classical communication over $\mathcal N$ (an $(n, C-\delta, \varepsilon)$ entanglement-assisted code exists for every $\varepsilon\in(0,1)$, $\delta>0$ and all sufficiently large $n$), then
--
--   $$C \le I(\mathcal N) = \max_{\varphi_{AA'}} I(A;B)_{\mathcal N_{A'\to B}(\varphi_{AA'})}.$$
--
--   Role: this is the converse half of the entanglement-assisted capacity theorem; in the parent it shows that the channel mutual information of the amplitude damping channel is an upper bound for every achievable rate, the first half of the least-upper-bound clause.
-- source:
--   Mark M. Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, https://arxiv.org/abs/1106.1445, Theorem 21.4.1 (Bennett-Shor-Smolin-Thapliyal), p. 593; converse proof in Section 21.5, pp. 600-605

import Mathlib
import Definitions.Def_WildeQIT_EADamping_channelMutualInfo
import Definitions.Def_WildeQIT_EADamping_IsAchievableEARate
open WildeQIT

namespace WildeQIT.EADamping

theorem isAchievableEARate_le_channelMutualInfo {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] [Nonempty a] (N : QChannel a b) (C : ℝ)
    (hC : IsAchievableEARate N C) : C ≤ channelMutualInfo N := by sorry

end WildeQIT.EADamping
