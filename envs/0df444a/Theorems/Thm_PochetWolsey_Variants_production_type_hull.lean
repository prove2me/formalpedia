-- Prove2me | Theorems.Thm_PochetWolsey_Variants_production_type_hull
-- name    : PochetWolsey.Variants.production_type_hull
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:19.992783+00:00
-- url     : https://prove2.me/theorems/e69522c5-2946-4f74-974d-3d008efea58e
-- title:
--   Proposition 11.6 — generalized inequalities and the production-type hull
-- statement:
--   For nonnegative demands in the uncapacitated $K$-type model, every generalized $(\ell,S)$ inequality is valid on the original binary-setup feasible set $X_{LS-U-CP}$. Moreover, if $P$ is the continuous relaxation of that original formulation, then
--   $$\operatorname{conv}(X_{LS-U-CP})=P\cap\bigcap_{\ell,(S_k\subseteq\{1,\dots,\ell\})_k}\left\{\sum_k\sum_{j\in S_k}x_j^k+\sum_k\sum_{j\notin S_k,\,j\le\ell}d_{j\ell}y_j^k\ge d_{1\ell}\right\}.$$
--
--   This is both validity and sufficiency, with the full production, setup, and inventory coordinates retained.
--
--   **Formalization Note** “Adding to the initial formulation” is read as adding the cuts to its continuous relaxation when describing a convex hull. The finite constant $M$ remains in the base constraints and is at least total demand. No terminal-stock equality or one-type-per-period restriction is inserted.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 345 (PDF 358), Proposition 11.6; DOI 10.1007/0-387-33477-7

import Definitions.Def_PochetWolsey_Variants_ProductionTypes

/- Imported module source, reproduced verbatim for declaration-only auditing.
import Mathlib

open scoped BigOperators

namespace PochetWolsey.Variants

abbrev CPPoint (n K : ℕ) :=
  (Fin K → Fin n → ℝ) × (Fin K → Fin n → ℝ) × (Fin (n + 1) → ℝ)

structure ProductionTypes (n K : ℕ) where
  d : Fin n → ℝ
  M : ℝ

def ProductionTypes.Standing {n K : ℕ} (D : ProductionTypes n K) : Prop :=
  0 < n ∧ 0 < K ∧ (∀ t, 0 ≤ D.d t) ∧ 0 < D.M ∧ (∑ t, D.d t) ≤ D.M

def ProductionTypes.base {n K : ℕ} (D : ProductionTypes n K)
    (w : CPPoint n K) : Prop :=
  (∀ k t, 0 ≤ w.1 k t ∧ 0 ≤ w.2.1 k t ∧ w.2.1 k t ≤ 1 ∧
    w.1 k t ≤ D.M * w.2.1 k t) ∧
  (∀ t, 0 ≤ w.2.2 t) ∧ w.2.2 0 = 0 ∧
  (∀ t : Fin n, w.2.2 t.castSucc + (∑ k, w.1 k t) =
    D.d t + w.2.2 t.succ)

def ProductionTypes.feasible {n K : ℕ} (D : ProductionTypes n K) : Set (CPPoint n K) :=
  {w | D.base w ∧ ∀ k t, w.2.1 k t = 0 ∨ w.2.1 k t = 1}

def ProductionTypes.cuts {n K : ℕ} (D : ProductionTypes n K)
    (w : CPPoint n K) : Prop :=
  ∀ (l : Fin n) (S : Fin K → Finset (Fin n)),
    (∀ k, S k ⊆ Finset.univ.filter (fun j => j ≤ l)) →
    (∑ j ∈ Finset.univ.filter (fun j => j ≤ l), D.d j) ≤
      (∑ k, ∑ j ∈ S k, w.1 k j) +
      ∑ k, ∑ j ∈ (Finset.univ.filter (fun j => j ≤ l)) \ S k,
        (∑ r ∈ Finset.univ.filter (fun r => j ≤ r ∧ r ≤ l), D.d r) * w.2.1 k j

end PochetWolsey.Variants
-/

namespace PochetWolsey.Variants

theorem production_type_hull {n K : ℕ} (D : ProductionTypes n K) (hD : D.Standing) :
    (∀ w ∈ D.feasible, D.cuts w) ∧
    convexHull ℝ D.feasible = {w | D.base w ∧ D.cuts w} := by sorry

end PochetWolsey.Variants
