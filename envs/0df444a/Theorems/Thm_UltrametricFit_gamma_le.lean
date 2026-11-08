-- Prove2me | Theorems.Thm_UltrametricFit_gamma_le
-- name    : UltrametricFit.gamma_le
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:46:22.311985+00:00
-- url     : https://prove2.me/theorems/2f5e1020-db0f-4de3-881c-4bf289c1bfd2
-- title:
--   Proof of Theorem 1, p.15 — $\Gamma=O(p)$
-- statement:
--   For each $\delta\in(0,1/2)$ there is a constant $C>0$ such that for every $p\ge1$,
--   $$0<\Gamma(\delta,p)=\frac{2}{(1+1/\Gamma_0)^{1/p}-1}\le C\,p.$$
--   The constant depends on $\delta$ only. This is where the linear dependence on $p$ in the main theorem comes from.
--
--   Differences from the source:
--   - encoding: $\Gamma=O(p)$ for any constant $\delta$ → for each $\delta$, a constant $C>0$ with $\Gamma\le C\,p$ for every $p\ge1$; reason: the meaning of the $O(\cdot)$ on the page
--   - generalization: an upper bound on $\Gamma$ → also $0<\Gamma$; reason: excludes a division-by-zero reading of the quotient; dropping it gives the page's claim
-- source:
--   Charikar, Gao, Fitting Ultrametrics under any ℓ_p Objective, STOC 2027 submission (manuscript sha256 87af12a2…), proof of Theorem 1, p.15

import Mathlib
import Definitions.Def_UltrametricFit_errLayer

namespace UltrametricFit

/-- **Proof of Theorem 1, `Γ = O(p)`**, Charikar, Gao, STOC 2027 submission (manuscript sha256
87af12a2…), p.15: `Γ = 2/((1 + 1/Γ₀)^{1/p} − 1) = O(p)` for any constant `δ ∈ (0, 0.5)`.

**Formalization Note.** The constant depends on `δ` only and comes before `p`. Positivity of `Γ`
excludes a division-by-zero reading of the quotient. -/
theorem gamma_le (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 1 ≤ p → 0 < Gamma δ p ∧ Gamma δ p ≤ C * p := by sorry

end UltrametricFit
