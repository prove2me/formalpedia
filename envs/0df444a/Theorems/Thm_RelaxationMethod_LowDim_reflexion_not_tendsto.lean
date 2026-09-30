-- Prove2me | Theorems.Thm_RelaxationMethod_LowDim_reflexion_not_tendsto
-- name    : RelaxationMethod.LowDim.reflexion_not_tendsto
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:31:51.966347+00:00
-- url     : https://prove2.me/theorems/64ad3357-f417-4bc2-8b32-51a03a927a57
-- title:
--   §8 — an infinite reflexion sequence ($\lambda = 2$) does not converge
-- statement:
--   Let $A$ be the nonempty solution polytope of a system of linear inequalities, and let $\{p_\nu\}$ be an infinite sequence produced by the reflexion process ($\lambda = 2$): every $p_\nu \notin A$, and $p_{\nu+1}$ is the mirror image of $p_\nu$ in the boundary of a half-space at maximal distance. Then $\{p_\nu\}$ does not converge.
--
--   This is the first step of the proof of Theorem 2, Case 2: a limit would lie in $A$ (§5), and from some index on every reflecting hyperplane would pass through it (§6), so the distance to the limit would stay constant and positive.
--
--   **Formalization Note** §8 assumes $r < n$ throughout, but the argument it cites (§5 and §6) does not use the dimension, so the statement has no dimension hypothesis. For $r = n$ it is also a consequence of Theorem 1, Case 2.
-- source:
--   Motzkin and Schoenberg, The relaxation method for linear inequalities, Canad. J. Math. 6 (1954), DOI 10.4153/CJM-1954-038-x, p. 401, §8 (by §5, p. 399, and §6, p. 399)

import Mathlib
import Definitions.Def_RelaxationMethod_LowDim_RelaxStep

open Filter Topology

namespace RelaxationMethod.LowDim

/-- §8, p. 401 (by §5 and §6): an infinite sequence produced by the reflexion process
(`λ = 2`) does not converge. -/
theorem reflexion_not_tendsto {n m : ℕ} (a : Fin m → EuclideanSpace ℝ (Fin n)) (b : Fin m → ℝ)
    (hA : (polytope a b).Nonempty) (p : ℕ → EuclideanSpace ℝ (Fin n))
    (hrun : ∀ ν, p ν ∉ polytope a b → IsRelaxStep a b 2 (p ν) (p (ν + 1)))
    (hinf : ∀ ν, p ν ∉ polytope a b) :
    ¬ ∃ l, Tendsto p atTop (𝓝 l) := by sorry

end RelaxationMethod.LowDim
