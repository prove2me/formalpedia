-- Prove2me | Theorems.Thm_PochetWolsey_Assembly_series_zero_stock
-- name    : PochetWolsey.Assembly.series_zero_stock
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:50.558348+00:00
-- url     : https://prove2.me/theorems/e98794b2-51ee-4f01-918b-33611be903a9
-- title:
--   Proposition 13.1 — serial zero-stock structure
-- statement:
--   Consider an uncapacitated serial lot-sizing system with at least two items, a positive finite horizon, unit utilization, zero lead times, nonnegative external demand only at the end-product, and zero endpoint stocks. Costs may be arbitrary real numbers. For the end-product set $d^0_t=d_t$; for any other item set $d^i_t=x^{i-1}_t$, the dependent demand in the selected plan. There is an optimal plan satisfying, for every item and period,
--   $$s^i_tx^i_t=0,\qquad x^i_t>0\Longrightarrow \exists\,t\le\alpha\le\beta<n:\quad x^i_t=\sum_{u=\alpha}^{\beta}d^i_u.$$
--   The same optimal plan satisfies both properties. This is the serial structural milestone.
--
--   **Formalization Note** Item $0$ represents the book’s item $1$, and period $t$ represents its period $t+1$. The superscript $i$ on the printed $d^i_{\alpha\beta}$ is retained through dependent demand, rather than replaced silently by final demand. Setup variables can be true with zero production.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 398 (PDF 408), Proposition 13.1; dependent-demand convention p. 397 (PDF 407)

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

theorem series_zero_stock {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (I : Model m n) (hseries : IsSeries I) :
    ∃ a : Plan m n, Optimal I none a ∧ ZeroStock a ∧ DependentBatches I a := by sorry

end PochetWolsey.Assembly
