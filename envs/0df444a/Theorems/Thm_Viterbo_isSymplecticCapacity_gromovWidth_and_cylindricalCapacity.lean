-- Prove2me | Theorems.Thm_Viterbo_isSymplecticCapacity_gromovWidth_and_cylindricalCapacity
-- name    : Viterbo.isSymplecticCapacity_gromovWidth_and_cylindricalCapacity
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T07:21:05.412866+00:00
-- url     : https://prove2.me/theorems/d6f21c80-538c-4837-aafc-84aa686d9184
-- title:
--   p. 2 — the Gromov width c_G and the cylindrical capacity c_Z are symplectic capacities
-- statement:
--   For every $n \ge 1$, both the Gromov width $c_G(U) = \sup\{\pi r^2 : B^{2n}(r) \hookrightarrow U\}$ and the cylindrical capacity $c_Z(U) = \inf\{\pi r^2 : U \hookrightarrow Z^{2n}(r)\}$ are symplectic capacities on $\mathbb R^{2n}$ in the sense of Definition 1.1: monotone under symplectic embeddings, conformal ($c(\alpha U) = \alpha^2 c(U)$ for $\alpha > 0$), and normalized ($c(B^{2n}(1)) = c(Z^{2n}(1)) = \pi$), with values in $[0, \infty]$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), p. 2, the Gromov width and the cylindrical capacity as symplectic capacities, which cites Gromov's non-squeezing theorem, Gromov, Pseudo holomorphic curves in symplectic manifolds, Invent. Math. 82 (1985) 307–347, https://doi.org/10.1007/BF01388806

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

namespace Viterbo

theorem isSymplecticCapacity_gromovWidth_and_cylindricalCapacity (n : ℕ) (hn : 1 ≤ n) :
    IsSymplecticCapacity n OAI.SymmetricPolar.gromovWidth ∧ IsSymplecticCapacity n cylindricalCapacity := by
  sorry

end Viterbo
