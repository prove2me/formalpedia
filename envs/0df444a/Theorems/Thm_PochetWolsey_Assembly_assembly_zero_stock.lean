-- Prove2me | Theorems.Thm_PochetWolsey_Assembly_assembly_zero_stock
-- name    : PochetWolsey.Assembly.assembly_zero_stock
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:59.659093+00:00
-- url     : https://prove2.me/theorems/d0bdca52-03cf-4743-a3c8-95ec63a7c47a
-- title:
--   Proposition 13.4 — assembly zero-stock structure
-- statement:
--   Consider an uncapacitated assembly lot-sizing system with at least two items, a positive finite horizon, one direct successor for each intermediate item, a unique end-product, unit utilization factors, zero lead times, and nonnegative external demand $d$ only at the end-product. Initial and terminal physical stocks are zero. Costs may be arbitrary real numbers. There exists an optimal plan such that, for all items and periods,
--   $$s^i_tx^i_t=0,\qquad x^i_t>0\Longrightarrow \exists\,t\le\alpha\le\beta<n:\quad x^i_t=\sum_{u=\alpha}^{\beta}d_u.$$
--   The assertion concerns one plan satisfying both structural properties. Here the interval sum is explicitly end-product demand, as printed in Proposition 13.4.
--
--   **Formalization Note** Item $0$ is the book’s item $1$, and production periods are zero-based. The successor map decreases in a topological numbering, permitting every finite assembly tree. This item imposes no Wagner–Whitin or setup-monotonicity restriction.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 406 (PDF 416), Proposition 13.4

import Definitions.Def_PochetWolsey_Assembly_Model

/- Imported definition bodies, reproduced verbatim for standalone inspection.
import Mathlib

open scoped BigOperators

namespace PochetWolsey.Assembly

structure Model (m n : ℕ) where
  successor : Fin (m + 1) → Fin (m + 1)
  root_successor : successor 0 = 0
  successor_lt : ∀ i, i ≠ 0 → (successor i).val < i.val
  demand : Fin n → ℝ
  demand_nonneg : ∀ t, 0 ≤ demand t
  productionCost : Fin (m + 1) → Fin n → ℝ
  holdingCost : Fin (m + 1) → Fin (n + 1) → ℝ
  setupCost : Fin (m + 1) → Fin n → ℝ

structure Plan (m n : ℕ) where
  production : Fin (m + 1) → Fin n → ℝ
  stock : Fin (m + 1) → Fin (n + 1) → ℝ
  setup : Fin (m + 1) → Fin n → Bool

def Capacity (m n : ℕ) := Fin (m + 1) → Fin n → NNReal

def IsSeries {m n : ℕ} (I : Model m n) : Prop :=
  ∀ i, i ≠ 0 → (I.successor i).val + 1 = i.val

noncomputable def effectiveDemand {m n : ℕ} (I : Model m n) (a : Plan m n)
    (i : Fin (m + 1)) (t : Fin n) : ℝ :=
  if i = 0 then I.demand t else a.production (I.successor i) t

def Feasible {m n : ℕ} (I : Model m n) (c : Option (Capacity m n))
    (a : Plan m n) : Prop :=
  (∀ i t, 0 ≤ a.production i t) ∧
  (∀ i t, 0 ≤ a.stock i t) ∧
  (∀ i, a.stock i 0 = 0 ∧ a.stock i (Fin.last n) = 0) ∧
  (∀ i t, a.stock i t.castSucc + a.production i t =
    effectiveDemand I a i t + a.stock i t.succ) ∧
  (∀ i t, a.setup i t = false → a.production i t = 0) ∧
  (∀ C, c = some C → ∀ i t,
    a.production i t ≤ (C i t : ℝ) * (if a.setup i t then 1 else 0))

noncomputable def cost {m n : ℕ} (I : Model m n) (a : Plan m n) : ℝ :=
  (∑ i, ∑ t, I.productionCost i t * a.production i t) +
  (∑ i, ∑ t, I.holdingCost i t * a.stock i t) +
  (∑ i, ∑ t, I.setupCost i t * (if a.setup i t then 1 else 0))

def Optimal {m n : ℕ} (I : Model m n) (c : Option (Capacity m n))
    (a : Plan m n) : Prop :=
  Feasible I c a ∧ ∀ b, Feasible I c b → cost I a ≤ cost I b

def Nested {m n : ℕ} (I : Model m n) (a : Plan m n) : Prop :=
  ∀ i t, i ≠ 0 → 0 < a.production i t → 0 < a.production (I.successor i) t

def ZeroStock {m n : ℕ} (a : Plan m n) : Prop :=
  ∀ i t, a.stock i t.castSucc * a.production i t = 0

noncomputable def echelonHolding {m n : ℕ} (I : Model m n)
    (i : Fin (m + 1)) (t : Fin (n + 1)) : ℝ :=
  I.holdingCost i t -
    ∑ j ∈ Finset.univ.filter (fun j => j ≠ 0 ∧ I.successor j = i), I.holdingCost j t

def WagnerWhitin {m n : ℕ} (I : Model m n) : Prop :=
  ∀ i (t u : Fin n), u.val = t.val + 1 →
    0 ≤ I.productionCost i t + echelonHolding I i t.succ - I.productionCost i u

def NonincreasingSetups {m n : ℕ} (I : Model m n) : Prop :=
  ∀ i (t u : Fin n), u.val = t.val + 1 → I.setupCost i u ≤ I.setupCost i t

def StationaryCosts {m n : ℕ} (I : Model m n) : Prop :=
  (∀ i (t u : Fin n), I.productionCost i t = I.productionCost i u) ∧
  (∀ i (t u : Fin (n + 1)), I.holdingCost i t = I.holdingCost i u) ∧
  (∀ i (t u : Fin n), I.setupCost i t = I.setupCost i u)

noncomputable def demandInterval {n : ℕ} (d : Fin n → ℝ) (α β : Fin n) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => α ≤ t ∧ t ≤ β), d t

def DependentBatches {m n : ℕ} (I : Model m n) (a : Plan m n) : Prop :=
  ∀ i t, 0 < a.production i t → ∃ α β : Fin n,
    t ≤ α ∧ α ≤ β ∧ a.production i t = demandInterval (effectiveDemand I a i) α β

def FinalDemandBatches {m n : ℕ} (I : Model m n) (a : Plan m n) : Prop :=
  ∀ i t, 0 < a.production i t → ∃ α β : Fin n,
    t ≤ α ∧ α ≤ β ∧ a.production i t = demandInterval I.demand α β

end PochetWolsey.Assembly
-/

namespace PochetWolsey.Assembly

theorem assembly_zero_stock {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (I : Model m n) :
    ∃ a : Plan m n, Optimal I none a ∧ ZeroStock a ∧ FinalDemandBatches I a := by sorry

end PochetWolsey.Assembly
