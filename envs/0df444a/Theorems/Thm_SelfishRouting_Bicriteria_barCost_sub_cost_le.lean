-- Prove2me | Theorems.Thm_SelfishRouting_Bicriteria_barCost_sub_cost_le
-- name    : SelfishRouting.Bicriteria.barCost_sub_cost_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:25.730238+00:00
-- url     : https://prove2.me/theorems/2f127426-3fa2-4bea-8ecd-4586167c8572
-- title:
--   Proof of Theorem 3.1, first display, p. 13 — $\sum_e \bar\ell_e(f^*_e) f^*_e - C(f^*) \le C(f)$
-- statement:
--   Let $A$ be a $0/1$ edge–route incidence matrix and $\ell_e$ edge latency functions that are nonnegative on $[0,\infty)$. Let $f$ and $f^*$ be two route flows with nonnegative entries, with edge flows $f_e$ and $f^*_e$, and let $\bar\ell$ be the modified latencies built from the edge flows of $f$: $\bar\ell_e(x) = \ell_e(f_e)$ for $x \le f_e$ and $\bar\ell_e(x) = \ell_e(x)$ for $x \ge f_e$. Then
--   $$
--   \sum_e \bar\ell_e(f^*_e)\, f^*_e - C(f^*) \le C(f).
--   $$
--
--   In words: evaluating $f^*$ with the latencies $\bar\ell$ rather than $\ell$ increases its cost by at most $C(f)$. This is the upper half of the proof of Theorem 3.1.
--
--   **Formalization Note.** The statement needs neither equilibrium nor feasibility nor monotonicity of $\ell$; only nonnegative route flows, a $0/1$ incidence matrix and $\ell_e \ge 0$ on $[0,\infty)$ are assumed, so it is slightly more general than the context on the page, where $f$ is a Nash flow and $f^*$ is feasible for $2r$.
-- source:
--   Roughgarden & Tardos, How Bad is Selfish Routing?, J. ACM 49(2) (2002), author's manuscript of 5 Dec 2001, p. 13, proof of Theorem 3.1, first display

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_SelfishRouting_Bicriteria_Model
import Definitions.Def_SelfishRouting_Bicriteria_BarLatency

namespace SelfishRouting.Bicriteria

open KellyStochasticNetworks

/-- Proof of Theorem 3.1, first display (p. 13):
`∑ₑ ℓ̄ₑ(f*ₑ) f*ₑ − C(f*) ≤ C(f)`, where `ℓ̄` is built from the edge flows of `f`. -/
theorem barCost_sub_cost_le {J R : ℕ} (A : Fin J → Fin R → ℝ) (ℓ : Fin J → ℝ → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hℓnn : ∀ j t, 0 ≤ t → 0 ≤ ℓ j t)
    (x y : Fin R → ℝ) (hx : ∀ r, 0 ≤ x r) (hy : ∀ r, 0 ≤ y r) :
    (∑ j, barLatency ℓ (linkFlow A x) j (linkFlow A y j) * linkFlow A y j) - cost A ℓ y
      ≤ cost A ℓ x := by sorry

end SelfishRouting.Bicriteria
