-- Prove2me | Theorems.Thm_Transcendence_liouville_house
-- name    : Transcendence.liouville_house
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T20:04:14.478093+00:00
-- url     : https://prove2.me/theorems/88a49c67-0ede-4536-a0bb-9287b4baff0b
-- title:
--   Liouville's inequality in house form, with an integer denominator
-- statement:
--   Let $K$ be a number field of degree $d$, let $\sigma : K \to \mathbb C$ be an embedding, and let $\alpha \in K$ be non-zero. If $c\,\alpha$ is an algebraic integer for some non-zero integer $c$, then
--
--   $$1 \le |c|^{d}\,|\sigma(\alpha)|\,\overline{|\alpha|}^{\,d-1},$$
--
--   where $\overline{|\alpha|}$ is the house of $\alpha$, the largest absolute value of its conjugates.
--
--   The norm of $c\alpha$ is a non-zero integer, and its absolute value is at most $|\sigma(c\alpha)|$ times the product of the other $d-1$ conjugates. With $c = 1$ this is the usual lower bound for a non-zero algebraic integer at one embedding. It is the arithmetic half of Gelfond's proof of the Gelfond–Schneider theorem.
-- source:
--   Standard (Liouville's inequality). Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi); the step appears in the formalization of the Gelfond-Schneider theorem by M. Karatarakis and F. Wiedijk, A formalization of the Gelfond-Schneider theorem, arXiv:2603.24823 (2026), mathlib4 fork at commit cb781672 (Apache 2.0).

import Mathlib

open NumberField

namespace Transcendence

theorem liouville_house {K : Type*} [Field K] [NumberField K] {α : K} (hα : α ≠ 0)
    {c : ℤ} (hc : c ≠ 0) (hcα : IsIntegral ℤ ((c : K) * α)) (σ : K →+* ℂ) :
    1 ≤ |(c : ℝ)| ^ Module.finrank ℚ K * ‖σ α‖ * house α ^ (Module.finrank ℚ K - 1) := by
  sorry

end Transcendence
