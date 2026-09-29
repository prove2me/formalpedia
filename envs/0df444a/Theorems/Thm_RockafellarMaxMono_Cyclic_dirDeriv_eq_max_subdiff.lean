-- Prove2me | Theorems.Thm_RockafellarMaxMono_Cyclic_dirDeriv_eq_max_subdiff
-- name    : RockafellarMaxMono.Cyclic.dirDeriv_eq_max_subdiff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:10:22.830585+00:00
-- url     : https://prove2.me/theorems/54b7cf0a-88b8-4326-90a8-f5948e5af072
-- title:
--   (3.7) — for finite continuous convex $f$, $f'(x;u) = \max\{\langle u, x^*\rangle \mid x^* \in \partial f(x)\}$
-- statement:
--   Let $V$ be a real Banach space with dual $V^*$, and let $f : V \to \mathbb{R}$ be a convex function which is everywhere finite and continuous. Fix $x \in V$. Then $\partial f(x)$ is a nonempty weak* compact subset of $V^*$, and for every direction $u \in V$ the one-sided directional derivative
--
--   $$
--   f'(x; u) = \lim_{\lambda \downarrow 0} \frac{f(x + \lambda u) - f(x)}{\lambda}
--   $$
--
--   exists (as a real number) and satisfies
--
--   $$
--   f'(x; u) = \max \{\, \langle u, x^* \rangle \mid x^* \in \partial f(x) \,\} ,
--   $$
--
--   the maximum being attained.
--
--   This is the max formula for the directional derivative, which Rockafellar cites from Moreau's lecture notes. In the proof of Theorem B it converts the inclusion $\partial f(x) \subseteq \partial g(x)$ into the inequality $f'(x;u) \le g'(x;u)$ between directional derivatives.
--
--   **Formalization Note** The limit is taken along real $\lambda \to 0$ with $\lambda > 0$ (the filter `𝓝[>] 0`). "max" is expressed as `IsGreatest` of the image set, so the maximum is attained. Weak* compactness is compactness of the image of $\partial f(x)$ under the identity map `StrongDual ℝ V → WeakDual ℝ V`. $V$ is an arbitrary real Banach space because the proof applies the result on the dual space $E^*$.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), pp. 214–215, (3.7) (citing Moreau [3, p. 65])

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
open Filter Topology

namespace RockafellarMaxMono.Cyclic

theorem dirDeriv_eq_max_subdiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (h : V → ℝ) (hconv : ConvexOn ℝ Set.univ h) (hcont : Continuous h)
    (x : V) :
    (Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x).Nonempty ∧
    IsCompact (StrongDual.toWeakDual '' Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x) ∧
    ∀ u : V, ∃ d : ℝ,
      Tendsto (fun t : ℝ => (h (x + t • u) - h x) / t) (𝓝[>] 0) (𝓝 d) ∧
      IsGreatest ((fun x' : StrongDual ℝ V => x' u) ''
        Shared.subdiff (fun y => ((h y : ℝ) : EReal)) x) d := by sorry

end RockafellarMaxMono.Cyclic
