-- Prove2me | Theorems.Thm_SubstOverbooking_Structure_lemma2_V0_concave
-- name    : SubstOverbooking.Structure.lemma2_V0_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:33.536699+00:00
-- url     : https://prove2.me/theorems/e2a06730-d83e-4e29-ab1c-7592f568183c
-- title:
--   Lemma 2, p. 87 — V₀(z, c) is jointly concave in z₁, …, zₙ and in c₁, …, cₘ
-- statement:
--   Fix net benefits $a_{ij}$.
--
--   1. For capacities with $c_j \ge 0$ ($j = 1, \dots, m$), the map $z \mapsto V_0(z, c)$ is concave on $\mathbb R^n_{\ge 0}$.
--   2. For $z \in \mathbb R^n_{\ge 0}$, the map $c \mapsto V_0(z, c)$ is concave on $\{c : c_j \ge 0,\ j = 1, \dots, m\}$.
--
--   That is, $V_0$ is jointly concave in the demand block $(z_1, \dots, z_n)$ and jointly concave in the capacity block $(c_1, \dots, c_m)$. Together with Lemma 1 this is the structure of the service-period value that the expected net revenue inherits.
--
--   **Formalization Note.** The virtual class $0$ is uncapacitated, so $c_0$ does not affect $V_0$ and is left free in part 2; the paper's statement is about $c_1, \dots, c_m$.
-- source:
--   Karaesmen & van Ryzin, Overbooking with Substitutable Inventory Classes, Operations Research 52(1):83–104 (2004), p. 87, Lemma 2

import Mathlib
import Definitions.Def_SubstOverbooking_Structure_Setting

namespace SubstOverbooking.Structure

theorem lemma2_V0_concave {n m : ℕ} (a : Fin n → Fin (m + 1) → ℝ) :
    (∀ c : Fin (m + 1) → ℝ, (∀ j, j ≠ 0 → 0 ≤ c j) →
      ConcaveOn ℝ {z : Fin n → ℝ | ∀ i, 0 ≤ z i} (fun z => V0 a c z)) ∧
    (∀ z : Fin n → ℝ, (∀ i, 0 ≤ z i) →
      ConcaveOn ℝ {c : Fin (m + 1) → ℝ | ∀ j, j ≠ 0 → 0 ≤ c j} (fun c => V0 a c z)) := by sorry

end SubstOverbooking.Structure
