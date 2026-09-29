-- Prove2me | Theorems.Thm_RockafellarMaxMono_Maximality_conj_subdiff_iff_nets
-- name    : RockafellarMaxMono.Maximality.conj_subdiff_iff_nets
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:03:43.029989+00:00
-- url     : https://prove2.me/theorems/e7ba6b84-a9a8-45e2-ad83-c61985e75fb7
-- title:
--   Proposition 1 — $\partial f^*$ is recovered from $\partial f$ through bounded weak** nets
-- statement:
--   Let $E$ be a real Banach space with dual $E^*$ and bidual $E^{**}$, let $f$ be a lower semicontinuous proper convex function on $E$, and let $x^* \in E^*$ and $x^{**} \in E^{**}$. Then $x^{**} \in \partial f^*(x^*)$ if and only if there exist
--
--   1. a nonempty directed partially ordered index set $I$,
--   2. a net $\{x_i^* \mid i \in I\}$ in $E^*$ converging to $x^*$ in the strong (norm) topology, and
--   3. a bounded net $\{x_i \mid i \in I\}$ in $E$, with the same index set, converging to $x^{**}$ in the weak** topology,
--
--   such that $x_i^* \in \partial f(x_i)$ for every $i \in I$. Here $E$ is regarded as a subspace of $E^{**}$ through the canonical embedding, and the weak** topology is the weak topology induced on $E^{**}$ by $E^*$:
--
--   $$
--   x_i \to x^{**} \text{ weak**} \iff \langle x_i, y^* \rangle \to x^{**}(y^*) \ \text{ for every } y^* \in E^* .
--   $$
--
--   In a nonreflexive space $\partial f^*$ maps $E^*$ into $E^{**}$ and is not the inverse of $\partial f$; this proposition says that $\partial f^*$ is nevertheless completely determined by $\partial f$.
--
--   **Formalization Note** A net is a function on a type $I$ carrying a partial order that is directed and nonempty, with convergence along the filter `atTop`; the index type lives in the same universe as $E$. Weak** convergence of $(x_i)$ to $x^{**}$ is stated as pointwise convergence on $E^*$ of the canonical images of the $x_i$, which is exactly convergence in the weak topology induced on $E^{**}$ by $E^*$. Boundedness is $\|x_i\| \le C$ for a real constant $C$ and all $i$.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 211, Proposition 1

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Shared_Conj
open Filter Topology
universe u

namespace RockafellarMaxMono.Maximality

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

end RockafellarMaxMono.Maximality
