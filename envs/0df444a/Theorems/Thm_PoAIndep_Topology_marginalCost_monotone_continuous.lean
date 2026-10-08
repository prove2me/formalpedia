-- Prove2me | Theorems.Thm_PoAIndep_Topology_marginalCost_monotone_continuous
-- name    : PoAIndep.Topology.marginalCost_monotone_continuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:11.715388+00:00
-- url     : https://prove2.me/theorems/277deba2-4d31-4cb1-adf7-1f3b4f9c343d
-- title:
--   §2.3, remark after Definition 2.6, p. 6 — the marginal cost of a standard latency is nondecreasing and continuous
-- statement:
--   Let $\ell$ be a standard latency function: nonnegative, differentiable and nondecreasing on $[0,\infty)$, with $x\,\ell(x)$ convex on $[0,\infty)$. Its marginal cost function $\ell^*(x)=\frac{d}{dx}(x\,\ell(x))$ is nondecreasing and continuous on $[0,\infty)$.
--
--   This is the remark following Definition 2.6. Monotonicity of $\ell^*$ drives Lemma 3.5, and continuity gives the existence of the scaling factor $\lambda$ in Definition 3.2.
--
--   **Formalization Note.** At $x=0$ the derivative, and continuity, are one-sided (within $[0,\infty)$).
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 6, §2.3, paragraph after Definition 2.6

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology

theorem marginalCost_monotone_continuous (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ) :
    MonotoneOn (marginalCost ℓ) (Set.Ici 0) ∧ ContinuousOn (marginalCost ℓ) (Set.Ici 0) := by sorry

end PoAIndep.Topology
