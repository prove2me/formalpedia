-- Prove2me | Theorems.Thm_SchrijverSFM_Ring_g_submodular
-- name    : SchrijverSFM.Ring.g_submodular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:05:48.874762+00:00
-- url     : https://prove2.me/theorems/1e320942-ea74-4a0e-8a4e-50a94c16aa5a
-- title:
--   Display (27), §6, p. 354 — g(X) = f(X̄) + c(X̄) is submodular on all subsets of V
-- statement:
--   Let $V$ be a finite set and $\mathcal C$ a ring family on $V$ with $\emptyset, V \in \mathcal C$ and $M_u \ne M_v$ for all $u \ne v$ ($M_v$ the smallest set of $\mathcal C$ containing $v$). Let $f : 2^V \to \mathbb R$ be submodular on $\mathcal C$, $c$ the weights of (23) extended modularly to sets, $\overline X$ the smallest set of $\mathcal C$ containing $X$, and
--   $$g(X) := f(\overline X) + c(\overline X) \qquad (X \subseteq V)$$
--   as in (26). Then $g$ is submodular on all subsets of $V$:
--   $$g(X) + g(Y) \ge g(X \cap Y) + g(X \cup Y) \qquad (X, Y \subseteq V).$$
--
--   This is display (27). It turns any algorithm minimizing submodular functions on $2^V$ into one that can be run on $g$ (and on $g - c$, since $c$ is modular), which is the point of §6.
--
--   **Formalization Note** Submodularity of $g$ is the referenced platform definition `NonmonotoneSubmod.Shared.Submodular`, the inequality (2) on all of `Finset V`.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 354, §6, display (27)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Ring_Setting

namespace SchrijverSFM.Ring

theorem g_submodular {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (hempty : ∅ ∈ C) (huniv : Finset.univ ∈ C)
    (hM : ∀ u v : V, u ≠ v → M C u ≠ M C v) (f : Finset V → ℝ) (hf : SubmodularOn C f) :
    NonmonotoneSubmod.Shared.Submodular (g C f) := by sorry

end SchrijverSFM.Ring
