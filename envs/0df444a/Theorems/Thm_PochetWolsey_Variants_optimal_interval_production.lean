-- Prove2me | Theorems.Thm_PochetWolsey_Variants_optimal_interval_production
-- name    : PochetWolsey.Variants.optimal_interval_production
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:23.988765+00:00
-- url     : https://prove2.me/theorems/ab68a3c4-53c5-4664-b563-0911465bf3c5
-- title:
--   Observation 11.3 — an optimal interval-production solution
-- statement:
--   For the combined uncapacitated model with $K$ production types and $L$ sales markets, under the stated nonnegative-demand, market-bound, cost-ordering, and standard endpoint conventions, there exists an optimal feasible solution with the following property. Whenever $x_t^k>0$, there are periods $a\le t\le b$ and market subsets $S(u)\subseteq\{1,\dots,L\}$ such that
--   $$x_t^k=\sum_{u=a}^b\left(d_u+\sum_{l\in S(u)}V_u^l\right).$$
--
--   This is the structural observation preceding the extended formulation. The assertion includes existence and attainment of an optimum, not merely an implication about a hypothetical minimizer.
--
--   **Formalization Note** Interval endpoints replace the book's offsets $t-a,t+b$ and are constrained to the horizon. The subsets may depend on the production type and period under consideration. As printed, holding and backlog costs have no sign condition; F4 records the resulting failure of optimal-solution existence.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 356 (PDF 369), Observation 11.3; DOI 10.1007/0-387-33477-7

import Definitions.Def_PochetWolsey_Variants_CombinedModel

/- Imported module source, reproduced verbatim for declaration-only auditing.
import Mathlib

open scoped BigOperators

namespace PochetWolsey.Variants

structure CombinedData (n K L : ℕ) where
  d : Fin n → ℝ
  V : Fin L → Fin n → ℝ
  p : Fin K → Fin n → ℝ
  q : Fin K → Fin n → ℝ
  e : Fin L → Fin n → ℝ
  h : Fin (n + 1) → ℝ
  b : Fin n → ℝ
  M : ℝ

structure CombinedPoint (n K L : ℕ) where
  x : Fin K → Fin n → ℝ
  y : Fin K → Fin n → ℝ
  v : Fin L → Fin n → ℝ
  s : Fin (n + 1) → ℝ
  r : Fin (n + 1) → ℝ

def CombinedData.Standing {n K L : ℕ} (D : CombinedData n K L) : Prop :=
  0 < n ∧ 0 < K ∧ 0 < L ∧
  (∀ t, 0 ≤ D.d t) ∧ (∀ l t, 0 ≤ D.V l t) ∧
  (∀ k t, 0 ≤ D.p k t ∧ 0 ≤ D.q k t) ∧
  (∀ k j t, k ≤ j → D.q k t ≤ D.q j t ∧ D.p j t ≤ D.p k t) ∧
  (∀ l j t, l ≤ j → D.e j t ≤ D.e l t) ∧
  0 < D.M ∧ (∑ t, (D.d t + ∑ l, D.V l t)) ≤ D.M

noncomputable def CombinedData.Vbar {n K L : ℕ} (D : CombinedData n K L)
    (l : Fin (L + 1)) (t : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin L => j.val < l.val), D.V j t

def CombinedPoint.domains {n K L : ℕ} (w : CombinedPoint n K L) : Prop :=
  (∀ k t, 0 ≤ w.x k t ∧ (w.y k t = 0 ∨ w.y k t = 1)) ∧
  (∀ l t, 0 ≤ w.v l t) ∧ (∀ t, 0 ≤ w.s t ∧ 0 ≤ w.r t) ∧
  w.s 0 = 0 ∧ w.s (Fin.last n) = 0 ∧ w.r 0 = 0 ∧ w.r (Fin.last n) = 0

def CombinedData.original {n K L : ℕ} (D : CombinedData n K L)
    (w : CombinedPoint n K L) : Prop :=
  w.domains ∧
  (∀ t : Fin n, w.s t.castSucc - w.r t.castSucc + (∑ k, w.x k t) =
    D.d t + (∑ l, w.v l t) + w.s t.succ - w.r t.succ) ∧
  (∀ l t, w.v l t ≤ D.V l t) ∧ (∀ k t, w.x k t ≤ D.M * w.y k t)

noncomputable def CombinedData.cost {n K L : ℕ} (D : CombinedData n K L)
    (w : CombinedPoint n K L) : ℝ :=
  (∑ k, ∑ t, (D.p k t * w.x k t + D.q k t * w.y k t)) +
    (∑ t, D.h t * w.s t) + (∑ t, D.b t * w.r t.succ) -
    ∑ l, ∑ t, D.e l t * w.v l t

def IsMinimum {A : Type*} (P : A → Prop) (c : A → ℝ) (w : A) : Prop :=
  P w ∧ ∀ w', P w' → c w ≤ c w'

abbrev Allocation (n K L : ℕ) := Fin K → Fin (L + 1) → Fin n → Fin n → ℝ
abbrev Assignment (n K : ℕ) := Fin K → Fin n → Fin n → ℝ

noncomputable def CombinedData.printedExtended {n K L : ℕ} (D : CombinedData n K L)
    (w : CombinedPoint n K L) (α : Allocation n K L) (z : Assignment n K) : Prop :=
  w.domains ∧
  (∀ k l u t, 0 ≤ α k l u t) ∧ (∀ k u t, 0 ≤ z k u t) ∧
  (∀ k u t, z k u t = ∑ l, α k l u t) ∧
  (∀ t, (∑ k, ∑ u, z k u t) = 1) ∧
  (∀ k t, z k t t ≤ w.y k t) ∧
  (∀ (k : Fin K) (u t t' : Fin n), u ≤ t → t'.val = t.val + 1 → z k u t' ≤ z k u t) ∧
  (∀ (k : Fin K) (u t t' : Fin n), t ≤ u → t.val = t'.val + 1 → z k u t' ≤ z k u t) ∧
  (∀ l t, w.v l t = ∑ k, ∑ u,
    ∑ j ∈ Finset.univ.filter (fun j : Fin L => l ≤ j),
      D.V j t * α k l.succ u t) ∧
  (∀ k u, w.x k u = ∑ l, ∑ t, (D.d t + D.Vbar l t) * α k l u t) ∧
  (∀ t : Fin n, w.s t.castSucc = ∑ k, ∑ l,
    ∑ u ∈ Finset.univ.filter (fun u : Fin n => u < t),
      ∑ τ ∈ Finset.univ.filter (fun τ : Fin n => t ≤ τ),
        (D.d τ + D.Vbar l τ) * α k l u τ) ∧
  (∀ t : Fin n, w.r t.succ = ∑ k, ∑ l,
    ∑ u ∈ Finset.univ.filter (fun u : Fin n => t < u),
      ∑ τ ∈ Finset.univ.filter (fun τ : Fin n => τ ≤ t),
        (D.d τ + D.Vbar l τ) * α k l u τ)

noncomputable def CombinedData.extended {n K L : ℕ} (D : CombinedData n K L)
    (w : CombinedPoint n K L) : Prop :=
  ∃ α : Allocation n K L, ∃ z : Assignment n K, D.printedExtended w α z

noncomputable def CombinedData.intervalProduction {n K L : ℕ} (D : CombinedData n K L)
    (w : CombinedPoint n K L) : Prop :=
  ∀ k t, 0 < w.x k t → ∃ a b : Fin n, a ≤ t ∧ t ≤ b ∧
    ∃ S : Fin n → Finset (Fin L),
      w.x k t = ∑ u ∈ Finset.univ.filter (fun u => a ≤ u ∧ u ≤ b),
        (D.d u + ∑ l ∈ S u, D.V l u)

end PochetWolsey.Variants
-/

namespace PochetWolsey.Variants

theorem optimal_interval_production {n K L : ℕ} (D : CombinedData n K L)
    (hD : D.Standing) :
    ∃ w : CombinedPoint n K L, IsMinimum D.original D.cost w ∧
      D.intervalProduction w := by sorry

end PochetWolsey.Variants
