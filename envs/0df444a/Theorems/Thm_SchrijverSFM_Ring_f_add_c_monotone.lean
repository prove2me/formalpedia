-- Prove2me | Theorems.Thm_SchrijverSFM_Ring_f_add_c_monotone
-- name    : SchrijverSFM.Ring.f_add_c_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:07:25.088413+00:00
-- url     : https://prove2.me/theorems/e4f1304d-b9ae-4234-b68d-e2ce279879e1
-- title:
--   Display (24), §6, p. 354 — f(Y) + c(Y) ≥ f(X) + c(X) for X ⊆ Y in 𝒞
-- statement:
--   Let $V$ be a finite set and $\mathcal C$ a ring family on $V$ with $\emptyset, V \in \mathcal C$ and $M_u \ne M_v$ for all $u \ne v$ ($M_v$ the smallest set of $\mathcal C$ containing $v$). Let $f : 2^V \to \mathbb R$ be submodular on $\mathcal C$, let $c(v) = \max\{0, f(L_v) - f(L_v \cup \{v\})\}$ as in (23), and $c(X) = \sum_{v \in X} c(v)$. Then for all $X, Y \in \mathcal C$ with $X \subseteq Y$,
--   $$f(Y) + c(Y) \ge f(X) + c(X).$$
--
--   So $f + c$ is monotone on $\mathcal C$. This is the inequality used in the last step of (27), and it is where the weights $c$ earn their place in the definition of $g$.
--
--   **Formalization Note** The hypothesis $M_u \ne M_v$ is necessary: with $V = \{a, b\}$, $\mathcal C = \{\emptyset, V\}$ (so $M_a = M_b = V$), $f(\emptyset) = 0$, $f(V) = -10$ and $f(\{a\}) = f(\{b\}) = 100$ (values off $\mathcal C$), one gets $c \equiv 0$ and $f(V) + c(V) < f(\emptyset) + c(\emptyset)$.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 354, §6, display (24)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Ring_Setting

namespace SchrijverSFM.Ring

theorem f_add_c_monotone {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (hempty : ∅ ∈ C) (huniv : Finset.univ ∈ C)
    (hM : ∀ u v : V, u ≠ v → M C u ≠ M C v) (f : Finset V → ℝ) (hf : SubmodularOn C f) :
    ∀ X ∈ C, ∀ Y ∈ C, X ⊆ Y → f X + csum C f X ≤ f Y + csum C f Y := by sorry

end SchrijverSFM.Ring
