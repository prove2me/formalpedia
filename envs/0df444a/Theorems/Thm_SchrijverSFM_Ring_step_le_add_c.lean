-- Prove2me | Theorems.Thm_SchrijverSFM_Ring_step_le_add_c
-- name    : SchrijverSFM.Ring.step_le_add_c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T00:07:20.76318+00:00
-- url     : https://prove2.me/theorems/25747939-97dc-4c75-8c7f-32aaff1f7c75
-- title:
--   Display (25), §6, p. 354 — f(X) ≤ f(Y) + c(v) when Y = X ∪ {v}, v ∉ X, X, Y ∈ 𝒞
-- statement:
--   Let $V$ be a finite set, $\mathcal C$ a ring family on $V$, and $f : 2^V \to \mathbb R$ submodular on $\mathcal C$. Let $L_v$ be the union of the sets of $\mathcal C$ not containing $v$ and $c(v) = \max\{0, f(L_v) - f(L_v \cup \{v\})\}$ as in (23). If $X, Y \in \mathcal C$, $v \notin X$ and $Y = X \cup \{v\}$, then
--   $$f(X) \le f(Y) + c(v).$$
--
--   This one-element step is display (25); chaining it along a maximal chain from $X$ to $Y$ in $\mathcal C$ gives the monotonicity (24) of $f + c$ on $\mathcal C$.
--
--   **Formalization Note** The paper's standing normalization ($\emptyset, V \in \mathcal C$, $M_u \ne M_v$) is not needed for this step and is not assumed, so the statement is slightly more general than the page.
-- source:
--   Schrijver, A combinatorial algorithm minimizing submodular functions in strongly polynomial time, J. Combin. Theory Ser. B 80 (2000), p. 354, §6, display (25)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SchrijverSFM_Ring_Setting

namespace SchrijverSFM.Ring

theorem step_le_add_c {V : Type} [Fintype V] [DecidableEq V]
    (C : Set (Finset V)) (hC : IsRingFamily C) (f : Finset V → ℝ) (hf : SubmodularOn C f)
    (X Y : Finset V) (hX : X ∈ C) (hY : Y ∈ C) (v : V) (hv : v ∉ X) (hXY : Y = insert v X) :
    f X ≤ f Y + cw C f v := by sorry

end SchrijverSFM.Ring
