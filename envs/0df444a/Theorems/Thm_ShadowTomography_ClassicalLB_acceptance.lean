-- Prove2me | Theorems.Thm_ShadowTomography_ClassicalLB_acceptance
-- name    : ShadowTomography.ClassicalLB.acceptance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T17:27:32.186324+00:00
-- url     : https://prove2.me/theorems/48c02d05-f8a4-4efb-b168-c35dae0a030d
-- title:
--   Designated subset accepts with probability 1/2 + 3ε
-- statement:
--   Let $S\subseteq[N]$ have size $N/2$, with $N\ge2$, and let $0\le\varepsilon\le1/6$. Draw $x$ from the biased distribution $\mathcal D_{S,\varepsilon}$ and accept exactly when $x\in S$. Then
--
--   $$
--   \Pr_{x\sim\mathcal D_{S,\varepsilon}}[x\in S]=\frac12+3\varepsilon.
--   $$
--
--   This is the acceptance probability of the measurement associated with the same subset in Theorem 16.
-- source:
--   Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, p. 20, proof of Theorem 16, display beginning 'Then by construction'

import Mathlib
import Definitions.Def_ShadowTomography_ClassicalLB_biasedDist

namespace ShadowTomography.ClassicalLB

/-- The designated subset accepts with probability `1/2 + 3ε`. -/
theorem acceptance (N : ℕ) (S : Finset (Fin N)) (ε : ℝ)
    (hhalf : 2 * S.card = N) (hne : 1 ≤ S.card)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 6) :
    ∑ x ∈ S, biasedDist N S ε x = 1 / 2 + 3 * ε := by sorry

end ShadowTomography.ClassicalLB
