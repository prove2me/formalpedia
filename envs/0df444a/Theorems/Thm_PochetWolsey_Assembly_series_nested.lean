-- Prove2me | Theorems.Thm_PochetWolsey_Assembly_series_nested
-- name    : PochetWolsey.Assembly.series_nested
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:52.565326+00:00
-- url     : https://prove2.me/theorems/bfe2fbb1-769b-4e1b-94b6-27eeb2c2e299
-- title:
--   Proposition 13.3 — serial nested optimality
-- statement:
--   Consider an uncapacitated serial lot-sizing system with at least two items, a positive finite horizon, unit utilization, zero lead times, nonnegative final demand, and zero endpoint stocks. Let $p^i_t,h^i_t,q^i_t$ denote production, physical holding, and setup costs, and let $H^i_t=h^i_t-h^{i+1}_t$, taking the missing upstream holding cost as zero. Assume either (i) $p^i_t+H^i_{t+1}-p^i_{t+1}\ge0$ and $q^i_t\ge q^i_{t+1}$ for every adjacent pair of periods and every item, or (ii) all three cost arrays are independent of time for each item. Then
--   $$\exists\text{ an optimal plan }(x,s,y):\quad x^i_t>0\Longrightarrow x^{i-1}_t>0\quad(i>0).$$
--   This states existence of a nested optimum in the serial model, with the two alternative cost regimes preserved.
--
--   **Formalization Note** Item and production indices are zero-based. Stock boundary $t$ precedes production period $t$; hence the echelon holding term in the adjacent-period inequality is $H^i_{t+1}$. Costs are real with no added nonnegativity hypothesis. Stationarity includes all stock-boundary indices, whose endpoint cost terms vanish because endpoint stocks are zero. Finding F3 disproves the printed stationary-cost alternative with two items, two periods, zero production/setup costs, and constant component holding cost $-1$: every optimum produces the component before its successor. This item preserves the source statement; no holding-cost sign condition is silently added.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 405 (PDF 415), Proposition 13.3 and Definition 13.2

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

theorem series_nested {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (I : Model m n) (hseries : IsSeries I)
    (hcost : (WagnerWhitin I ∧ NonincreasingSetups I) ∨ StationaryCosts I) :
    ∃ a : Plan m n, Optimal I none a ∧ Nested I a := by sorry

end PochetWolsey.Assembly
