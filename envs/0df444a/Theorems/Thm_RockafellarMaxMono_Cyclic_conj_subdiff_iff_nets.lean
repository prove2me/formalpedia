-- Prove2me | Theorems.Thm_RockafellarMaxMono_Cyclic_conj_subdiff_iff_nets
-- name    : RockafellarMaxMono.Cyclic.conj_subdiff_iff_nets
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:12:56.314977+00:00
-- url     : https://prove2.me/theorems/e82465ca-1a87-4c79-810d-d8962fe54bd1
-- title:
--   Proposition 1 — $\partial f^*$ is recovered from $\partial f$ through bounded weak** nets
-- statement:
--   Let $E$ be a real Banach space with dual $E^*$ and bidual $E^{**}$, and let $f$ be a lower semicontinuous proper convex function on $E$ with conjugate $f^*$ on $E^*$. Let $x^* \in E^*$ and $x^{**} \in E^{**}$. Then
--
--   $$
--   x^{**} \in \partial f^*(x^*)
--   $$
--
--   if and only if there exist a net $\{x_i^* \mid i \in I\}$ in $E^*$ converging to $x^*$ in the strong (norm) topology and a **bounded** net $\{x_i \mid i \in I\}$ in $E$, with the same directed index set $I$, converging to $x^{**}$ in the weak** topology, such that $x_i^* \in \partial f(x_i)$ for every $i \in I$.
--
--   Here $E$ is regarded as a subspace of $E^{**}$ through the canonical embedding, and the weak** topology on $E^{**}$ is the weak topology induced by $E^*$. In the proof of Theorem B, Proposition 1 transfers the inclusion $\partial(g+j) \supset \partial(f+j)$ on $E$ to $\partial(g+j)^* \supset \partial(f+j)^*$ on $E^*$, without assuming $E$ reflexive.
--
--   **Formalization Note** A net is encoded by a nonempty type $I$ (in the universe of $E$) with a partial order that is directed, and convergence is along the `atTop` filter. Strong convergence is convergence in the operator norm of `StrongDual ℝ E`. Weak** convergence of $x_i$ to $x^{**}$ is pointwise convergence $\langle x_i, y^* \rangle \to x^{**}(y^*)$ for every $y^* \in E^*$. Boundedness is $\sup_i \|x_i\| < \infty$.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 211, Proposition 1

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Shared_Conj
open Filter Topology
universe u

namespace RockafellarMaxMono.Cyclic

theorem conj_subdiff_iff_nets {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : E → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f)
    (x' : StrongDual ℝ E) (x'' : StrongDual ℝ (StrongDual ℝ E)) :
    x'' ∈ Shared.subdiff (Shared.conj f) x' ↔
      ∃ (I : Type u) (_ : PartialOrder I) (_ : IsDirected I (· ≤ ·)) (_ : Nonempty I)
        (xs' : I → StrongDual ℝ E) (xs : I → E),
        Tendsto xs' atTop (𝓝 x') ∧
        (∃ C : ℝ, ∀ i, ‖xs i‖ ≤ C) ∧
        (∀ y' : StrongDual ℝ E,
          Tendsto (fun i => NormedSpace.inclusionInDoubleDual ℝ E (xs i) y') atTop (𝓝 (x'' y'))) ∧
        ∀ i, xs' i ∈ Shared.subdiff f (xs i) := by sorry

end RockafellarMaxMono.Cyclic
