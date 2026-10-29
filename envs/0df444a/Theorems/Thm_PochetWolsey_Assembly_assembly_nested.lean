-- Prove2me | Theorems.Thm_PochetWolsey_Assembly_assembly_nested
-- name    : PochetWolsey.Assembly.assembly_nested
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:55.912667+00:00
-- url     : https://prove2.me/theorems/2b45fff2-0b88-49b3-8f3f-3d936762d8ef
-- title:
--   Proposition 13.5 — nested optimal assembly plan (literal ML-A claim)
-- statement:
--   Consider a feasible assembly lot-sizing system with at least two items, a positive finite horizon, unit utilization factors, zero lead times, a unique end-product with nonnegative external demand, and zero endpoint stocks. Production periods are numbered $0,\ldots,n-1$; stock boundary $t$ precedes period $t$. Production, physical holding, and setup costs are real numbers. Write $H^i_t=h^i_t-\sum_{j:D(j)=i}h^j_t$. Assume, for every item and adjacent pair of periods,
--   $$p^i_t+H^i_{t+1}-p^i_{t+1}\ge0,\qquad q^i_t\ge q^i_{t+1}.$$
--   The asserted conclusion is
--   $$\exists\text{ an optimal plan }(x,s,y):\quad x^i_t>0\Longrightarrow x^{D(i)}_t>0\quad(i\text{ intermediate}).$$
--
--   The printed ML-A qualifier is retained: capacities may be absent or may be finite nonnegative item-period bounds. The statement is the source anchor; its capacitated reading is contradicted by finding F1.
--
--   **Formalization Note** Nonemptiness of the feasible set makes explicit the implicit meaning of an optimization problem admitting a solution; it does not assume optimality or nesting. Zero-based item $0$ is the book’s item $1$. No nonnegative-setup-cost condition is added: that condition appears only in the subsequent recursion. The missing uncapacitated qualifier is deliberately not repaired in this item.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, DOI 10.1007/0-387-33477-7, p. 407 (PDF 417), Proposition 13.5; original capacitated assembly model p. 406 (PDF 416)

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

theorem assembly_nested {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (I : Model m n) (c : Option (Capacity m n))
    (hfeasible : ∃ a : Plan m n, Feasible I c a)
    (hww : WagnerWhitin I) (hsetup : NonincreasingSetups I) :
    ∃ a : Plan m n, Optimal I c a ∧ Nested I a := by sorry

end PochetWolsey.Assembly
