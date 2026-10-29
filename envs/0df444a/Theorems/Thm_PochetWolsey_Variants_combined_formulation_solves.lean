-- Prove2me | Theorems.Thm_PochetWolsey_Variants_combined_formulation_solves
-- name    : PochetWolsey.Variants.combined_formulation_solves
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:41.187528+00:00
-- url     : https://prove2.me/theorems/59932fe8-0493-477c-ae35-ad2e8e46730e
-- title:
--   Theorem 11.12 — the printed combined formulation solves LS-U-B, SL, CP
-- statement:
--   For the finite uncapacitated lot-sizing model with nonnegative fixed demands, $K$ ordered production cost segments, $L$ markets with nonnegative upper bounds and ordered prices, and the standard zero endpoints, the original problem (11.52)–(11.56) and the displayed extended model (11.57)–(11.67) have attained minima of the same value:
--   $$\exists w^*,q^*:\quad w^*\in\operatorname{argmin}_{w\in X}C(w),\quad q^*\in\operatorname{argmin}_{q\in\operatorname{proj}Q}C(q),\quad C(w^*)=C(q^*).$$
--   Here $X$ is defined by the original balances, market bounds and setup links, while $Q$ is defined by all the printed extended constraints. Each minimum compares against every feasible point of its respective model.
--
--   This retains the book's claimed optimization equivalence as the mission goal. F1 gives a one-period counterexample to the printed sales formula, F2 records that the displayed setup domain is binary although the theorem calls the model a linear program, and F4 records the missing boundedness condition for signed storage costs. The claim is therefore expected to be disproved as printed.
--
--   **Formalization Note** The printed $\alpha_{ut}^{kl}$ in (11.63) and binary domain in (11.67) are retained. No extra market-capacity or balance constraints are imposed on the extension. The standard fixed-endpoint convention is explicit, $M$ bounds total potential requirements, and holding/backlog costs remain arbitrary real numbers. No corrected variant replaces this faithful target.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 357 (PDF 370), Theorem 11.12; DOI 10.1007/0-387-33477-7

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

theorem combined_formulation_solves {n K L : ℕ} (D : CombinedData n K L)
    (hD : D.Standing) :
    ∃ w q : CombinedPoint n K L,
      IsMinimum D.original D.cost w ∧ IsMinimum D.extended D.cost q ∧
      D.cost w = D.cost q := by sorry

end PochetWolsey.Variants
