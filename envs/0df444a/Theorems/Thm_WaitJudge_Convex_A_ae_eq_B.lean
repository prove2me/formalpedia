-- Prove2me | Theorems.Thm_WaitJudge_Convex_A_ae_eq_B
-- name    : WaitJudge.Convex.A_ae_eq_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:58:49.45005+00:00
-- url     : https://prove2.me/theorems/8f387e84-7860-48e8-a6b9-7bd55a76f658
-- title:
--   Sect. 5.1.1, pp. 14–15 — A = B up to a zero-probability set
-- statement:
--   Let Assumptions 1 and 2 hold, fix $k\le N$ and a threshold $\epsilon(k)$, and write $x^*_k$, $s^*_k$ for the solution and the number of support constraints of the program built on the first $k$ scenarios only. Let
--   $$A=\{V(x^*_N)>\epsilon(k)\ \wedge\ s^*_N=k\ \wedge\ \text{the first $k$ constraints are of support}\},$$
--   $$B=\{V(x^*_k)>\epsilon(k)\ \wedge\ s^*_k=k\ \wedge\ \text{the constraints with indexes $k+1,\dots,N$ are satisfied by $x^*_k$}\}.$$
--   Then $A$ and $B$ differ by a $\mathbb P^N$-null set:
--   $$\mathbb P^N\big(A\,\triangle\,B\big)=0.$$
--
--   This equality reduces the probability of $A$, which involves the full program, to that of $B$, which involves the first $k$ scenarios and an independent check of the remaining $N-k$; that is the route to formula (16).
--
--   **Formalization Note** Indices are $0$-based: the first $k$ scenarios are $\delta^{(0)},\dots,\delta^{(k-1)}$ and the remaining ones have index $j\ge k$. The statement is an almost-everywhere equality of sets and needs no measurability hypothesis.
-- source:
--   Campi & Garatti, Wait-and-judge scenario optimization, Math. Program. (2018), doi:10.1007/s10107-016-1056-9 (accepted manuscript), PDF pp. 14–15, Sect. 5.1.1, event B and 'Proof of the fact that A = B up to a zero probability set'

import Mathlib
import Definitions.Def_ScenarioApproach_Generalization_violation
import Definitions.Def_WaitJudge_Convex_Setting

open MeasureTheory ScenarioApproach.Generalization

namespace WaitJudge.Convex

theorem A_ae_eq_B {d p : ℕ} {Δ : Type*} [MeasurableSpace Δ] (P : Measure Δ) [IsProbabilityMeasure P]
    (c : E d) (X : Set (E d)) (Xδ : Δ → Set (E d)) (tb : Fin p → E d → ℝ)
    (hA1 : Assumption1 c X Xδ tb) (hA2 : Assumption2 c X Xδ tb P)
    (ε : ℕ → ℝ) (N k : ℕ) (hk : k ≤ N) :
    {ω : Fin N → Δ | ε k < violation P Xδ (xstar c X Xδ tb ω) ∧ sstar c X Xδ tb ω = k ∧
        ∀ i : Fin N, i.val < k → i ∈ supportSet c X Xδ tb ω}
      =ᵐ[Measure.pi fun _ : Fin N => P]
    {ω : Fin N → Δ | ε k < violation P Xδ (xstar c X Xδ tb (firstK hk ω)) ∧
        sstar c X Xδ tb (firstK hk ω) = k ∧
        ∀ j : Fin N, k ≤ j.val → xstar c X Xδ tb (firstK hk ω) ∈ Xδ (ω j)} := by sorry

end WaitJudge.Convex
