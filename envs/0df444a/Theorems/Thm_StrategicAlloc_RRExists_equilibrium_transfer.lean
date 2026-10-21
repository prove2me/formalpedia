-- Prove2me | Theorems.Thm_StrategicAlloc_RRExists_equilibrium_transfer
-- name    : StrategicAlloc.RRExists.equilibrium_transfer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:36:03.529664+00:00
-- url     : https://prove2.me/theorems/350e2667-52c7-409b-832b-6d18c7369b08
-- title:
--   §A, p. 24, proof of Theorem A.3 — a PNE of the perturbed instance is a PNE of the original one
-- statement:
--   Let $v = (v_1,\dots,v_n)$ and $v' = (v'_1,\dots,v'_n)$ be two valuation profiles on the same $n \ge 1$ agents and $m$ goods, and for each agent $i$ let $\varepsilon_i > 0$ be the smallest positive difference between the $v_i$-values of two bundles (or $1$ if there is none). Suppose that for every agent $i$ and every bundle $T \subseteq M$,
--   $$v_i(T) \le v'_i(T) \le v_i(T) + \frac{2\varepsilon_i}{3}.$$
--   If the bid profile $\mathbf d$ is a pure Nash equilibrium of Round-Robin for the instance $(N, M, v')$, then $\mathbf d$ is also a pure Nash equilibrium of Round-Robin for the instance $(N, M, v)$.
--
--   Together with the perturbation step and Theorem A.2, this yields Theorem A.3.
--
--   **Formalization Note** As in the perturbation step, $\varepsilon_i$ is the bundle-level gap `bundleGap (v i)` rather than the page's good-level gap; with the page's $\varepsilon$ the inequality $v_k(A_k) \le v_k(B_k) - \varepsilon_k$ used in the proof does not follow. No positivity or strictness of $v$ or $v'$ is assumed.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 24, §A, proof of Theorem A.3, third and fourth paragraphs (bundle-level ε: disclosed repair)

import Mathlib
import Definitions.Def_StrategicAlloc_RRExists_Setting

namespace StrategicAlloc.RRExists

/-- Proof of Theorem A.3, third and fourth paragraphs (p. 24), with the bundle-level ε: if every
agent's perturbed valuation `v'` satisfies v_i(T) ≤ v'_i(T) ≤ v_i(T) + 2ε_i/3 for all bundles T,
with ε_i = `bundleGap (v i)`, then every pure Nash equilibrium of Round-Robin under `v'` is a pure
Nash equilibrium of Round-Robin under `v`. -/
theorem equilibrium_transfer {n m : ℕ} [NeZero n] (v v' : Fin n → Fin m → ℝ)
    (hclose : ∀ i (T : Finset (Fin m)), StrategicAlloc.RRFair.val v i T ≤ StrategicAlloc.RRFair.val v' i T ∧
      StrategicAlloc.RRFair.val v' i T ≤ StrategicAlloc.RRFair.val v i T + 2 * bundleGap (v i) / 3)
    (d : Fin n → Fin m → ℝ) (hd : StrategicAlloc.RRFair.IsPNE StrategicAlloc.RRFair.roundRobin v' d) :
    StrategicAlloc.RRFair.IsPNE StrategicAlloc.RRFair.roundRobin v d := by sorry

end StrategicAlloc.RRExists
