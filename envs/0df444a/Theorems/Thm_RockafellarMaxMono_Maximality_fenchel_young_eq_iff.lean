-- Prove2me | Theorems.Thm_RockafellarMaxMono_Maximality_fenchel_young_eq_iff
-- name    : RockafellarMaxMono.Maximality.fenchel_young_eq_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T18:01:51.839412+00:00
-- url     : https://prove2.me/theorems/68ee3da5-75ca-4f51-9649-2adc82518ee0
-- title:
--   (2.2) — Fenchel–Young inequality with its equality case
-- statement:
--   Let $V$ be a real Banach space with dual $V^*$, and let $f$ be a lower semicontinuous proper convex function on $V$ with conjugate $f^*$. Then for every $x \in V$ and $x^* \in V^*$,
--
--   $$
--   f(x) + f^*(x^*) \ \ge\ \langle x, x^* \rangle ,
--   $$
--
--   with equality if and only if $x^* \in \partial f(x)$.
--
--   This is display (2.2) of the paper. Applied with $V = E^*$ and $f^*$ in place of $f$ it also gives display (2.4), which relates $f^{**}$, $f^*$ and $\partial f^*$; both are used to pass between subgradients and equality in the Fenchel–Young inequality.
--
--   **Formalization Note** The paper writes $f(x) + f^*(x^*) - \langle x, x^*\rangle \ge 0$; we state the equivalent form with the pairing on the other side, so that no extended-real subtraction appears. The space is an arbitrary real Banach space $V$ (the paper's $E$), so that the statement applies to $E^*$ as well.
-- source:
--   Rockafellar, On the maximal monotonicity of subdifferential mappings, Pacific J. Math. 33 (1970), p. 210, (2.2)

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_ProperConvex
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_RockafellarMaxMono_Shared_Conj

namespace RockafellarMaxMono.Maximality

theorem fenchel_young_eq_iff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (f : V → EReal) (hf : Shared.ProperConvex f) (hlsc : LowerSemicontinuous f) :
    ∀ (x : V) (x' : StrongDual ℝ V),
      ((x' x : ℝ) : EReal) ≤ f x + Shared.conj f x' ∧
        (f x + Shared.conj f x' = ((x' x : ℝ) : EReal) ↔ x' ∈ Shared.subdiff f x) := by sorry

end RockafellarMaxMono.Maximality
