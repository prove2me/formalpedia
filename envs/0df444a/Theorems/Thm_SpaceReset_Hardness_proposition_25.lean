-- Prove2me | Theorems.Thm_SpaceReset_Hardness_proposition_25
-- name    : SpaceReset.Hardness.proposition_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:21:14.944326+00:00
-- url     : https://prove2.me/theorems/40d723b3-b914-42e2-8628-76780dbb6e38
-- title:
--   Proposition 25 — exact composition under independent concatenation
-- statement:
--   Let $G_i\in\mathbb F_2^{k_i\times n_i}$, $i=1,\dots,m$, be ordered sources of full row rank $k_i$ with invariants $(c_i,\Pi_i)$. Their direct-sum code, in that block order, satisfies
--   $$c=\max_ic_i,\qquad \Pi=\max\Big\{\sum_ik_i,\ \max_i\Pi_i\Big\}.$$
--
--   Appending an independent coordinate to a source therefore leaves $c$ unchanged and raises $\Pi$ only up to the total rank; Theorem 2's yes case uses this.
--
--   Differences from the source:
--   - encoding: maxima over an index set of blocks → Finset.sup over Fin m (value 0 for m = 0); reason: the empty family has c = Π = 0, which the formula gives
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), Proposition 25, App. B.1, p. 38

import Mathlib
import Definitions.Def_SpaceReset_Hardness_Trellis

set_option autoImplicit false

namespace SpaceReset.Hardness

/-- Proposition 25 (Exact composition under independent concatenation), App. B.1, p. 38. -/
theorem proposition_25 {m : ℕ} {k n : Fin m → ℕ}
    (G : (i : Fin m) → Matrix (Fin (k i)) (Fin (n i)) F2) (hG : ∀ i, FullRowRank (G i)) :
    cInv (directSum G) = Finset.univ.sup (fun i => cInv (G i)) ∧
    PiInv (directSum G) = max (∑ i, k i) (Finset.univ.sup (fun i => PiInv (G i))) := by sorry

end SpaceReset.Hardness
