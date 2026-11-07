-- Prove2me | Theorems.Thm_RGMISFast_eq_20
-- name    : RGMISFast.eq_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:48.646865+00:00
-- url     : https://prove2.me/theorems/c78a1cb2-b0fe-49d2-ba52-46f2afa85c82
-- title:
--   Eq. (20): $f'(s)=-E[\sum_W d_s(W)\mid r(u^*)=\rho]$
-- statement:
--   Let $G$ be a finite simple graph with root $u^*$, fix $k\ge1$, $t>0$ and a root rank $\rho\ge t$, and let the other ranks be i.i.d. Exp(1). For $0\le s\le t$ let
--   $$
--   f(s)=\mathbb E\big[Y_k(s)\mid r(u^*)=\rho\big].
--   $$
--   Then for every $s\in[0,t)$,
--   $$
--   f'(s)=-\mathbb E\Big[\sum_W d_s(W)\ \Big|\ r(u^*)=\rho\Big], \tag{20}
--   $$
--   where $W$ ranges over the sets for which $\{u^*\}\cup W$ is counted by $Y_k(s)$ and $d_s(W)$ is $d(W)$ computed in the active graph $G_s$.
--
--   With Lemma 5.1 this yields the differential inequality (21) that proves Lemma 5.2.
--
--   **Formalization Note** The conditional law fixes the root's rank at $\rho$. $f$ and the right-hand side are integrals of real-valued counts, and the measurability of both counts at every time is stated. The derivative is the derivative of $f$ within $[0,t]$ at $s$ (one-sided at $s=0$).
--
--   Differences from the source:
--   - reading: E[· | r(u∗) = ρ] → integral under `rootLaw u ρ` (root rank ρ, other ranks i.i.d. Exp(1)); reason: the conditional law stated in the proof (p.18)
--   - reading: f′(s) for s < t (f differentiable on [0, t]) → HasDerivWithinAt f (−g s) on [0, t] at every s ∈ [0, t); reason: the proof computes the derivative at s < t inside [0, t]; at s = 0 it is one-sided
--   - generalization: the expectations f(s) and E[Σ_W d_s(W)] → Bochner integrals plus measurability of Y_k(s) and Σ_W d_s(W) for every s; reason: the added measurability clauses are true and exclude a junk value of the integrals; dropping them gives (20)
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Proof of Lemma 5.2, eq. (20), pp.18–19 (PDF pp.20–21)

import Mathlib
import Definitions.Def_RGMISFast_Y
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Eq. (20) (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), Proof of Lemma 5.2, pp.18–19): fix `k ≥ 1`, `t > 0` and a root rank
`ρ ≥ t`; conditionally on `r(u∗) = ρ`, let `f(s) = E[Y_k(s) | r(u∗) = ρ]` for `0 ≤ s ≤ t`. Then
`f′(s) = −E[Σ_W d_s(W) | r(u∗) = ρ]`, where `W` ranges over the sets for which `{u∗} ∪ W` is
counted by `Y_k(s)` and `d_s(W)` is `d(W)` computed in `G_s`.

**Formalization Note** The conditional law is `rootLaw u ρ` (root rank `ρ`, other ranks i.i.d.
Exp(1)). `f` and `s ↦ E[Σ_W d_s(W)]` are Bochner integrals of real-valued counts; measurability
of both integrands at every time is stated, so neither integral can be a junk value. The
derivative is taken within `[0, t]` at every `s ∈ [0, t)` (the proof's short-window computation
fixes `s < t`; at `s = 0` it is one-sided). -/
theorem eq_20 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (hk : 1 ≤ k) (t ρ : ℝ) (ht : 0 < t) (htρ : t ≤ ρ) :
    (∀ s : ℝ, Measurable (fun r : V → ℝ => (Y G u k s r : ℝ))) ∧
    (∀ s : ℝ, Measurable (fun r : V → ℝ => (dsSum G u k s r : ℝ))) ∧
    ∀ s ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt (fun s' : ℝ => ∫ r, (Y G u k s' r : ℝ) ∂(rootLaw u ρ))
        (-(∫ r, (dsSum G u k s r : ℝ) ∂(rootLaw u ρ))) (Set.Icc 0 t) s := by sorry

end RGMISFast
