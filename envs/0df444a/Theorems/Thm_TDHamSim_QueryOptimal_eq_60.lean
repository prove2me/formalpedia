-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_eq_60
-- name    : TDHamSim.QueryOptimal.eq_60
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:23:14.41236+00:00
-- url     : https://prove2.me/theorems/93853e84-bd34-4d9b-87e1-426d3dad8d10
-- title:
--   §6.1, eq. (60) — update-product factorization
-- statement:
--   For $J=2^m$ and $0<w\le1$, with $c=(1-w/2)/(1+w/2)$, the entire update product satisfies
--
--   $$S^\circ=\widehat W_J^{\rm out}\widehat{\operatorname{Rot}}(c^J)\Phi_P(\widehat W_J^{\rm in})^\dagger.$$
--
--   This is an equality of the computed operators on the public–private space. The physical-register version extends both sides by the identity on unused public states. It includes every oracle-ancilla sector, not only the zero-ancilla sector.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - generalization: the section regime J≥2 with q and αT as specified on p.25 → all powers of two J≥1 and every 0<w≤1; reason: the exact factorization also has the J=1 base case and does not use q
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), §6.1, eq. (60) — update-product factorization, p.26. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_LCU

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- §6.1, eq. (60), p.26: complete update-product factorization. -/
theorem eq_60 (m a n : ℕ) (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) :
    updates (2^m) a n w = dyadicW m a n true (cosine w) *
      totalRot m a n ((cosine w)^(2^m)) * privatePhase (2^m) a n *
      (dyadicW m a n false (cosine w)).conjTranspose := by sorry

end TDHamSim.QueryOptimal
