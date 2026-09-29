-- Prove2me | Theorems.Thm_StochasticOrders_PositiveDependence_supermodular_order_closure_properties
-- name    : StochasticOrders.PositiveDependence.supermodular_order_closure_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:17:07.328699+00:00
-- url     : https://prove2.me/theorems/af755fe1-c909-467a-b418-cb99b57390a4
-- title:
--   Theorem 9.A.9(a),(c) — closure of the supermodular order under monotone composition and marginalization
-- statement:
--   (a) Let $(X_1,\dots,X_n)$ and $(Y_1,\dots,Y_n)$ be two $n$-dimensional random vectors. If
--   $(X_1,\dots,X_n) \le_{sm} (Y_1,\dots,Y_n)$, then
--
--   $$(g_1(X_1),\dots,g_n(X_n)) \le_{sm} (g_1(Y_1),\dots,g_n(Y_n))$$
--
--   whenever $g_1,\dots,g_n : \mathbb{R}\to\mathbb{R}$ are all increasing or are all decreasing.
--
--   (c) Let $X=(X_1,\dots,X_n)$ and $Y=(Y_1,\dots,Y_n)$ be two $n$-dimensional random vectors. If
--   $X \le_{sm} Y$, then $X_I \le_{sm} Y_I$ for every $I \subseteq \{1,\dots,n\}$: the
--   supermodular order is closed under marginalization.
--
--   Together, these are two of the five closure properties Theorem 9.A.9 establishes for the
--   supermodular order (the book's parts (b), (d), (e) — closure under independent conjunction,
--   mixtures, and convergence in distribution — are not drafted in this mission; see the mission
--   `STATUS.md` for why). Part (a) is what makes $\le_{sm}$ compatible with monotone relabeling of
--   each coordinate (the fact that composing a supermodular function with coordinatewise monotone
--   functions, all increasing or all decreasing, is again supermodular); part (c) is what makes a
--   comparison of whole vectors restrict consistently to any sub-vector.
--
--   **Formalization Note** Both parts are stated as pushforwards of the laws $P,Q$ of $X,Y$ under
--   the relevant map: part (a) under `fun x i => g i (x i)` (coordinatewise application), part (c)
--   under the coordinate-restriction map `fun x : Fin n → ℝ => fun i : {i // i ∈ I} => x i}`,
--   landing in `SupermodularOrder` at the (arbitrary-`Fintype`) index type `{i // i ∈ I}` rather
--   than a fixed `Fin k` — exactly the generality `Def_StochasticOrders_PositiveDependence_Orders`
--   was built for.
-- source:
--   Shaked & Shanthikumar, Stochastic Orders, Springer 2007, pp. 395-396, Theorem 9.A.9(a),(c)

import Mathlib
import Definitions.Def_StochasticOrders_PositiveDependence_Orders

namespace StochasticOrders.PositiveDependence

open MeasureTheory

/-- Theorem 9.A.9(a),(c) (Shaked & Shanthikumar, *Stochastic Orders*, Springer 2007, pp. 395-396):
(a) if `(X₁,…,Xₙ) ≤sm (Y₁,…,Yₙ)`, then `(g₁(X₁),…,gₙ(Xₙ)) ≤sm (g₁(Y₁),…,gₙ(Yₙ))` whenever the
`gᵢ : ℝ → ℝ` are all increasing or are all decreasing; (c) if `X ≤sm Y` (both `n`-dimensional),
then `X_I ≤sm Y_I` for every `I ⊆ {1,…,n}` — the supermodular order is closed under
marginalization. Both are stated as pushforwards of the laws `P`, `Q` of `X`, `Y`. -/
theorem supermodular_order_closure_properties {n : ℕ} (P Q : Measure (Fin n → ℝ)) :
    (∀ g : Fin n → ℝ → ℝ, ((∀ i, Monotone (g i)) ∨ (∀ i, Antitone (g i))) →
      (∀ i, Measurable (g i)) →
      SupermodularOrder P Q →
      SupermodularOrder (Measure.map (fun x i => g i (x i)) P)
        (Measure.map (fun x i => g i (x i)) Q)) ∧
    (∀ (I : Set (Fin n)) [DecidablePred (· ∈ I)],
      SupermodularOrder P Q →
      SupermodularOrder (Measure.map (fun x : Fin n → ℝ => fun i : {i // i ∈ I} => x i) P)
        (Measure.map (fun x : Fin n → ℝ => fun i : {i // i ∈ I} => x i) Q)) := by sorry

end StochasticOrders.PositiveDependence
