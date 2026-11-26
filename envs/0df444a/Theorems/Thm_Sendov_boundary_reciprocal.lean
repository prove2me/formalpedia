-- Prove2me | Theorems.Thm_Sendov_boundary_reciprocal
-- name    : Sendov.boundary_reciprocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:58:56.612874+00:00
-- url     : https://prove2.me/theorems/06074789-0c33-4dc8-a9fb-a0ff2992ff7b
-- title:
--   Sendov: boundary reciprocal
-- statement:
--   **`(BR)`, in division-free form.**  From `∏ Zs = n ∏ Qi` and `2 ∑ₑ Zs = n ∑ₑ Qi` — the two
--   readings of `p'(1)` and `p''(1)` — one gets `∑ⱼ 1/Qiⱼ = 2 ∑ⱼ 1/Zsⱼ`.  Applied with
--   `Zsⱼ = 1 - zⱼ` and `Qiⱼ = 1/qⱼ` this is `∑ⱼ qⱼ = 2 ∑ⱼ 1/(1-zⱼ)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Boundary.lean#L151-L162
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Boundary.lean#L151-L162

import Definitions.Def_Sendov_Counterexample_Factor
import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Boundary
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.boundary_reciprocal {n : ℕ} {Zs Qi : Multiset ℂ} (hn0 : (n : ℂ) ≠ 0)
    (hZ : ∀ u ∈ Zs, u ≠ 0) (hQ : ∀ u ∈ Qi, u ≠ 0)
    (hI : Zs.prod = (n : ℂ) * Qi.prod)
    (hII : 2 * sumEraseProd Zs = (n : ℂ) * sumEraseProd Qi) :
    (Qi.map (fun u => u⁻¹)).sum = 2 * (Zs.map (fun u => u⁻¹)).sum := by sorry
