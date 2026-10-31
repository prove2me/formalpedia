-- Prove2me | Theorems.Thm_TransitoryQueue_theorem_2_8
-- name    : TransitoryQueue.theorem_2_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:41.771106+00:00
-- url     : https://prove2.me/theorems/0c22619f-f39b-42e5-9d3e-af71b7f208ff
-- title:
--   Theorem 2.8 (corrected: Assumption 2.5 centring) — strong embedding of the arrival process
-- statement:
--   Let $F_n$ ($n\ge1$) and $G$ be distribution functions supported on $[0,\infty)$ with $\sup_{t\ge0}|F_n(t)-G(t)|=O(1/\sqrt n)$, let $p\in[0,1]$, and let $\nu$ be a law on $[0,\infty)$ whose moment generating function is finite near $0$, with mean $\mu>0$ and standard deviation $\sigma$. On every strongly coupled version of the model (`IsStrongCoupling`: one $\hat B$, one bridge $B^{\mathrm{br}}$, the couplings (88), (89), (98)), almost surely
--
--   $$\sup_{t\ge0}\bigl|A_n(t)-H_n(t)\bigr|=O\bigl(n^{1/4}\sqrt{\log n}\bigr),\qquad H_n(t)=npF_n(t)+\sqrt n\Bigl(pB^{\mathrm{br},n}_{G(t)}+\sqrt{p(1-p)}\,\hat B_{G(t)}\Bigr),$$
--
--   that is, for almost every $\omega$ there is $C(\omega)$ with $|A_n(t)-H_n(t)|\le C\,n^{1/4}\sqrt{\log n}$ for all $n\ge2$ and $t\ge0$.
--
--   Differences from the source:
--   - correction: under Assumption 2.5, H_n(t) = np(G(t) + r_n(G)) + √n(pB^{br,n}_{G(t)} + √(p(1−p)) B̂_{G(t)}) → H_n(t) = npF_n(t) + √n(…), i.e. centred at npG^{(n)}(t); reason: the printed branch is false: G = 1 − e^{−t}, G^{(n)} = (1 − n^{−1/2})G + n^{−1/2}(1 − e^{−2t}) satisfy Assumption 2.5 with r_n(G) = 1/(4√n), and at t = 0, A_n(0) = 0 while H_n(0) = np r_n(G) = p√n/4
--   - generalization: two cases: Assumption 2.1 (cdf G) and Assumption 2.5 (G^{(n)} strictly increasing, Lipschitz, r_n(G) = O(1/√n)) → distribution functions F_n, G with r_n = O(1/√n), no monotonicity or Lipschitz condition; reason: F_n = G is Assumption 2.1 with r_n = 0 and the printed H_n; F_n = G^{(n)} is Assumption 2.5
--   - generalization: "There exists a Brownian motion B̂, a Brownian bridge B^{br,n} such that …" → for every strongly coupled version (IsStrongCoupling), whose existence is the milestone exists_strong_coupling; reason: a bound for every strongly coupled version; such a version exists by exists_strong_coupling, and then this item gives the printed existence of B̂ and B^{br,n}; stating it for the coupled version lets the later milestones use the same version
--   - encoding: a.s. O(n^{1/4} √log n), sup over t ∈ [0, ∞) → ∀ᵐ ω, ∃ C, ∀ n ≥ 2, ∀ t ≥ 0, |A_n(t) − H_n(t)| ≤ C n^{1/4} √(log n); reason: n = 1 is excluded since log 1 = 0; C depends on ω
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Theorem 2.8, p.6

import Mathlib
import Definitions.Def_TransitoryQueue_IsArrivalCDF
import Definitions.Def_TransitoryQueue_rn
import Definitions.Def_TransitoryQueue_arrivals
import Definitions.Def_TransitoryQueue_Hn
import Definitions.Def_TransitoryQueue_IsStrongCoupling
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TransitoryQueue

/-- **Theorem 2.8 (strong embedding of the arrival process).** On a strongly coupled version of the
model, almost surely `sup_{t ≥ 0} |A_n(t) - H_n(t)| = O(n^{1/4} √(log n))`, where
`H_n(t) = n p F_n(t) + √n (p B^{br,n}_{G(t)} + √(p(1-p)) B̂_{G(t)})`.
Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Theorem 2.8, p.6.

**Formalization Note** One statement for both assumptions (`F_n = G`: Assumption 2.1;
`F_n = G^{(n)}`: Assumption 2.5). Under Assumption 2.5 the printed centring `n p (G(t) + r_n(G))`
is false (at `t = 0`, `A_n(0) = 0` while it is `n p r_n(G)`, of order `√n`); the centring is
`n p F_n(t)`. The version is `IsStrongCoupling`, which provides the paper's Brownian motion `B̂`
and bridge with (88), (89). `a.s. O`: `∀ᵐ ω, ∃ C`, for all `n ≥ 2` and `t ≥ 0`. -/
theorem theorem_2_8 (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (hF : ∀ n, IsArrivalCDF (F n)) (hG : IsArrivalCDF G)
    (hr : ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → rn (F n) G ≤ K / Real.sqrt n)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : ν (Set.Iio 0) = 0)
    (hmgf : ∃ δ : ℝ, 0 < δ ∧ ∀ l : ℝ, |l| < δ → Integrable (fun y => Real.exp (l * y)) ν)
    (hμ : 0 < ∫ y, y ∂ν)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (T : (n : ℕ) → Fin n → Ω → ℝ) (ζ : (n : ℕ) → Fin n → Ω → ℕ) (V : (n : ℕ) → Fin n → Ω → ℝ)
    (B Bh : ℝ≥0 → Ω → ℝ) (Bbr : ℕ → ℝ → Ω → ℝ)
    (hS : IsStrongCoupling P F p ν T ζ V B Bh Bbr) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ t : ℝ, 0 ≤ t →
      |(arrivals (fun i => T n i ω) (fun i => ζ n i ω) t : ℝ) - Hn F G p n (Bbr n) Bh t ω|
        ≤ C * (n : ℝ) ^ ((1 : ℝ) / 4) * Real.sqrt (Real.log n) := by sorry

end TransitoryQueue
