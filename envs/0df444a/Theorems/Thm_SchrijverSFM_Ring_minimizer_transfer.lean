-- Prove2me | Theorems.Thm_SchrijverSFM_Ring_minimizer_transfer
-- name    : SchrijverSFM.Ring.minimizer_transfer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:06:04.980981+00:00
-- url     : https://prove2.me/theorems/92c0a097-cafb-4f5d-a837-2248af756933
-- title:
--   §6, last paragraph, p. 354 — if U minimizes g(U) − c(U) over all U ⊆ V then Ū minimizes f over 𝒞
-- statement:
--   Let $V$ be a finite set and $\mathcal C$ a ring family on $V$ with $V \in \mathcal C$. Let $f : 2^V \to \mathbb R$ be any function, $c$ the weights of (23) extended modularly to sets, $\overline X$ the smallest set of $\mathcal C$ containing $X$, and $g(X) = f(\overline X) + c(\overline X)$ as in (26). If $U \subseteq V$ minimizes $g(U) - c(U)$ over **all** subsets of $V$, that is,
--   $$g(U) - c(U) \le g(W) - c(W) \qquad \text{for all } W \subseteq V,$$
--   then $\overline U \in \mathcal C$ and $\overline U$ minimizes $f$ over $\mathcal C$:
--   $$f(\overline U) \le f(T) \qquad \text{for all } T \in \mathcal C.$$
--
--   This is the final step of Schrijver's reduction: a minimizer of the submodular function $g - c$ on $2^V$, found by the algorithm of §§2–5, yields a minimizer of $f$ over the ring family.
--
--   **Formalization Note** Only closure under union and intersection and $V \in \mathcal C$ are used; submodularity of $f$, $\emptyset \in \mathcal C$ and $M_u \ne M_v$ are not assumed here (they are needed for (27), not for this transfer).
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 354, §6, last paragraph

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Ring_Setting

namespace SchrijverSFM.Ring

theorem minimizer_transfer {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (huniv : Finset.univ ∈ C)
    (f : Finset V → ℝ) (U : Finset V)
    (hU : ∀ W : Finset V, g C f U - csum C f U ≤ g C f W - csum C f W) :
    closure C U ∈ C ∧ ∀ T ∈ C, f (closure C U) ≤ f T := by sorry

end SchrijverSFM.Ring
