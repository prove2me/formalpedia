-- Prove2me | Theorems.Thm_ServiceParts_Palm_arrival_times_order_statistics
-- name    : ServiceParts.Palm.arrival_times_order_statistics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T22:25:14.65998+00:00
-- url     : https://prove2.me/theorems/4b4ffda4-2899-4aeb-b70b-715d50cf50bf
-- title:
--   Eq. (3.3) — given N(t) = n, the order epochs have density n!/tⁿ on 0 < t₁ < ⋯ < tₙ < t
-- statement:
--   In the $(s-1,s)$ backorder system, let $T_0 < T_1 < \cdots$ be the order epochs and $N(t)$ the number of orders in $[0,t]$. Fix $t > 0$ and $n \ge 0$. Conditionally on $N(t) = n$, the vector of the first $n$ order epochs has the joint density
--   $$f_{T_0,\dots,T_{n-1}}(t_1,\dots,t_n) = \frac{n!}{t^n}, \qquad 0 < t_1 < t_2 < \cdots < t_n < t,$$
--   and $0$ elsewhere: for every measurable $A \subseteq \mathbb R^n$,
--   $$P\big[N(t) = n,\ (T_0,\dots,T_{n-1}) \in A\big] = P[N(t) = n]\cdot\frac{n!}{t^n}\,\mathrm{Leb}\big(A \cap \{0 < t_1 < \cdots < t_n < t\}\big).$$
--
--   Equivalently, the epochs have the law of the order statistics of $n$ independent uniform random variables on $[0,t]$; considered as unordered times they are independent and uniform on $[0,t]$. This is the fact the proof of Palm's theorem uses to treat each outstanding order separately.
--
--   **Formalization Note** Orders are indexed from $0$, so the book's $X_1,\dots,X_n$ are $T_0,\dots,T_{n-1}$. The conditional density is stated through the joint probability with the event $N(t)=n$, which has positive probability for $t > 0$.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 38-39, Section 3.1 and Eq. (3.3)

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Palm

theorem arrival_times_order_statistics {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t) (n : ℕ)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    P ({ω | S.orderCount t ω = n} ∩ {ω | (fun i : Fin n => S.arrival i ω) ∈ A}) =
      P {ω | S.orderCount t ω = n} *
        (ENNReal.ofReal ((Nat.factorial n : ℝ) / t ^ n) *
          volume (A ∩ {x : Fin n → ℝ | StrictMono x ∧ ∀ i, 0 < x i ∧ x i < t})) := by sorry

end ServiceParts.Palm
