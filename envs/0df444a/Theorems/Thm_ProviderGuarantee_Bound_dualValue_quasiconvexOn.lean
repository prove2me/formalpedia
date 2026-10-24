-- Prove2me | Theorems.Thm_ProviderGuarantee_Bound_dualValue_quasiconvexOn
-- name    : ProviderGuarantee.Bound.dualValue_quasiconvexOn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:42:35.26735+00:00
-- url     : https://prove2.me/theorems/e50243ee-02cc-436d-9326-790e3a5e4713
-- title:
--   Proof of Theorem 1, pp. 38–39 — f(γ), the optimal value of the dual (16), is quasiconvex on [γmin, γmax]^n with values in [0, 1]
-- statement:
--   Let $0 < \gamma_{\min} \le \gamma_{\max}$ and let $f(\gamma)$ be the optimal value of the dual problem (15), equivalently (16), of p. 38. Then $f$ maps the box $[\gamma_{\min}, \gamma_{\max}]^n$ into $[0, 1]$, and $f$ is quasiconvex on it: for every $t \in \mathbb R$ the sublevel set
--
--   $$\{\gamma \in [\gamma_{\min}, \gamma_{\max}]^n : f(\gamma) \le t\}$$
--
--   is convex.
--
--   The page argues that each term of the objective of (16) is quasiconvex jointly in $(\gamma, \lambda)$, that its feasible region is convex in $(\gamma, \lambda)$, and that minimizing over $\lambda$ preserves quasiconvexity. Quasiconvexity is what reduces the maximization of $f$ over the box to its vertices.
--
--   **Formalization Note** $f$ is `dualValue`, and quasiconvexity is Mathlib's `QuasiconvexOn` (convex sublevel sets) on the box `Set.Icc (fun _ => γmin) (fun _ => γmax)`.
--
--   Differences from the source:
--   - encoding: f(γ) is the optimal value of problem (16) → dualValue γ, the infimum of s over the feasible (s, λ) of (15); reason: (16) is (15) with s eliminated (p. 38: 'Problem (15) in turn can be rewritten as'); dividing the first two families of constraints of (15) by γ_i, γ_k > 0 gives the max in (16), so the values coincide
--   - encoding: 'f(γ) : [γmin, γmax]^n → [0, 1]' and 'f(γ) must be quasiconvex in γ' → 0 ≤ dualValue γ ≤ 1 on the box, and QuasiconvexOn ℝ (box) dualValue; reason: Mathlib's quasiconvexity is convexity of every sublevel set, the standard definition
-- source:
--   Gur, Iancu & Warnes, Value Loss in Allocation Systems with Provider Guarantees, SSRN 3351509 (version of March 24, 2020), pp. 38–39, proof of Theorem 1, (16)

import Mathlib
import Definitions.Def_ProviderGuarantee_Bound_Model

namespace ProviderGuarantee.Bound

theorem dualValue_quasiconvexOn {n : ℕ} (γmin γmax : ℝ) (hγmin : 0 < γmin) (hγ : γmin ≤ γmax) :
    QuasiconvexOn ℝ (Set.Icc (fun _ : Fin n => γmin) (fun _ => γmax)) dualValue ∧
    ∀ γ ∈ Set.Icc (fun _ : Fin n => γmin) (fun _ => γmax),
      0 ≤ dualValue γ ∧ dualValue γ ≤ 1 := by sorry

end ProviderGuarantee.Bound
