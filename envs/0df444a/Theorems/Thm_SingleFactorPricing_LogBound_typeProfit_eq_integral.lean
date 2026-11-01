-- Prove2me | Theorems.Thm_SingleFactorPricing_LogBound_typeProfit_eq_integral
-- name    : SingleFactorPricing.LogBound.typeProfit_eq_integral
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:17:00.40413+00:00
-- url     : https://prove2.me/theorems/0fa96f0e-e065-41b0-8d80-5a080c2d4685
-- title:
--   §2, p.4 — $\mathcal R^*_j=\int_0^\infty G_j(q)\,dq$
-- statement:
--   Let $f$ be a positive vector and let $\bar p_t$ be a positive price vector of type $t$. Then $G_t$ is integrable on $(0,\infty)$ and
--
--   $$
--   R_t(\bar p_t)=\int_0^\infty G_t(q)\,dq .
--   $$
--
--   When $\bar p_t$ is optimal for type $t$, the left side is $\mathcal R^*_t$. The identity rewrites the profit of a type as an integral over the pricing direction, which is the first step towards comparing it with profits along $f$.
--
--   Differences from the source:
--   - generalization: $\bar p^j$ optimal, $\mathcal R^*_j$ on the left → any positive price vector, $R_t(\bar p_t)$ on the left, demand of any sign; reason: optimality and non-negativity are not used; at an optimal $\bar p^j$ the left side is $\mathcal R^*_j$
--   - encoding: $\int_0^\infty$ → integral over `Set.Ioi 0`, with integrability of $G_t$ added to the conclusion; reason: the same integral; integrability makes the Bochner value meaningful
-- source:
--   Gallego, Berbeglia, Bounds and Heuristics for Multi-Product Personalized Pricing, arXiv:2102.03038v2, §2, p.4

import Mathlib
import Definitions.Def_SingleFactorPricing_LogBound_typeProfit
import Definitions.Def_SingleFactorPricing_LogBound_typeFilteredDemand

open MeasureTheory

namespace SingleFactorPricing.LogBound

/-- **M1: the profit of a type as an integral.** Gallego, Berbeglia, arXiv:2102.03038v2, §2, p.4:
"define `G_j(q) := ∑_{i∈N} f_i d_ij(p̄ʲ)δ_ij(q)` for `q ≥ 0` and notice that
`R*_j = ∫₀^∞ G_j(q)dq`."

**Formalization Note.** `R*_j` is `typeProfit d t (pbar t)`. The identity needs only `0 < f i` and
`0 < pbar t i`, not optimality, so it is stated for a positive price vector. Integrability of `G_t`
on `(0, ∞)` is part of the conclusion, because the Bochner integral of a non-integrable function
is `0`. -/
theorem typeProfit_eq_integral {N T : Type*} [Fintype N] (d : T → (N → ℝ) → N → ℝ) (f : N → ℝ)
    (pbar : T → N → ℝ) (t : T) (hf : ∀ i, 0 < f i) (hp : ∀ i, 0 < pbar t i) :
    IntegrableOn (typeFilteredDemand d f pbar t) (Set.Ioi 0) ∧
      typeProfit d t (pbar t) = ∫ q in Set.Ioi (0 : ℝ), typeFilteredDemand d f pbar t q := by sorry

end SingleFactorPricing.LogBound
