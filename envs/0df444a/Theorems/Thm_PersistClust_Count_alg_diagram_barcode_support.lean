-- Prove2me | Theorems.Thm_PersistClust_Count_alg_diagram_barcode_support
-- name    : PersistClust.Count.alg_diagram_barcode_support
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-09T11:10:27.089258+00:00
-- url     : https://prove2.me/theorems/5fc391fd-58da-4e9d-9c08-15bad573a580
-- title:
--   Rips barcode support: births are vertex values, deaths below birth
-- statement:
--   This is the **support (zero-mass) control** for the elder-rule barcode of the upper-star Rips filtration.
--
--   The barcode $\mathrm{ripsBarcode}(g,Dm,\delta,\sigma)$ is produced by the union-find sweep of Procedure 1 (RR-6968) with merge threshold $\tau=+\infty$. A purely structural property of the sweep is that every point of the extended plane at which the barcode is nonzero has a *real* birth coordinate equal to $g_r$ for some vertex $r$, and its death coordinate is either $-\infty$ (an immortal bar, contributed by a surviving entry) or a real level $d$ strictly below the birth level (an off-diagonal elder-rule pair).
--
--   Indeed, each step of the sweep only ever increments the accumulated multiplicity at points $((g_r,-\infty))$ for absorbed roots with $g_i<g_r$ is dropped, so every recorded pair satisfies $g_i<g_r$, and the surviving entries contribute only $((g_r,-\infty))$.
-- source:
--   Chazal--Guibas--Oudot--Skraba, RR-6968 (2009), Procedure 1 (τ=+∞ elder-rule sweep), structural support property

import Mathlib
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_AlgBarcode

namespace PersistClust.Count

theorem alg_diagram_barcode_support
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (p : EReal × EReal) (hp : ripsBarcode g Dm δ σ p ≠ 0) :
    ∃ r : Fin n, p.1 = ((g r : EReal)) ∧
      (p.2 = ⊥ ∨ ∃ d : ℝ, p.2 = ((d : EReal)) ∧ ((d : EReal)) < ((g r : EReal))) := by sorry

end PersistClust.Count
