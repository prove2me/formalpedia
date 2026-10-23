-- Prove2me | Theorems.Thm_StaticReusable_Guarantee_combination
-- name    : StaticReusable.Guarantee.combination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:46.012763+00:00
-- url     : https://prove2.me/theorems/a0cfb596-47e4-4e4f-9b41-62072e24ecec
-- title:
--   §3.1, p. 15 (combination) — for C ≥ 4, R ≥ R̃ ≥ min{104/131, 6/7} ≥ 15/19
-- statement:
--   Let $C \ge 4$ and $z_1, \dots, z_C \ge 0$ (with $z_{C+1} = 1$). Then
--   $$R(z_1, \dots, z_C) \ge \tilde R(z_1, \dots, z_C) \ge \min\left\{\frac{104}{131}, \frac67\right\} \quad\text{and}\quad R(z_1, \dots, z_C) \ge \frac{15}{19}.$$
--
--   Together with the cases $C \le 3$ of Step 2a (and $R \equiv 1$ for $C = 1$), this bounds the stock-in ratio by $15/19$ for every $C$, which with (10)–(12) yields Theorem 1.
--
--   **Formalization Note** The page draws this conclusion from Step 2b and Lemmas 2–4, each of which is stated for every $z \in [0,\infty)^C$; the combination is therefore stated for every nonnegative $z$, with no monotonicity assumption on the underlying rates. All three members of the printed chain are kept.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, p. 15, §3.1, end of Step 2b (combination)

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace StaticReusable.Guarantee

theorem combination {C : ℕ} (hC : 4 ≤ C) (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k) :
    Rt C z ≤ R C z ∧ min (104 / 131 : ℝ) (6 / 7) ≤ Rt C z ∧ (15 / 19 : ℝ) ≤ R C z := by sorry
end StaticReusable.Guarantee
