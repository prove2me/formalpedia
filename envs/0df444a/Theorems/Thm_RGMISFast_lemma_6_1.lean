-- Prove2me | Theorems.Thm_RGMISFast_lemma_6_1
-- name    : RGMISFast.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:02.617727+00:00
-- url     : https://prove2.me/theorems/57b460d3-377b-42bf-aaee-2d02e42079eb
-- title:
--   Lemma 6.1: conditional growth and boundary bounds (24)–(27)
-- statement:
--   Fix $0\le\theta<a$, a history at time $\theta$, a nonempty set $A$ connected in $G_\theta$, and prescribed ranks of the vertices of $A$ in $[a,\infty)$, as in Lemma 5.3. Let $b\in(a,\infty]$ and
--   $$
--   q=\frac{e\,(1-e^{-(b-a)})}{a-\theta},
--   $$
--   with $1-e^{-(b-a)}=1$ for $b=\infty$. For every integer $k\ge1$,
--   $$
--   \Pr[|\Gamma_{a,b}(A)|\ge k]\le q^k, \tag{24}
--   $$
--   $$
--   \mathbb E\Big[\binom{K_{a,b}(A)}{k}\Big]\le q^k. \tag{25}
--   $$
--   In particular, for $\theta=a/2$ and $c=1+1/(2e^2)$,
--   $$
--   \Pr[|\Gamma_{a,ca}(A)|>x]\le e^{-x}\qquad(x\ge0), \tag{26}
--   $$
--   and, with $\theta=a/2$, $a=a_m$, $b=b_i$, $0\le i<m$,
--   $$
--   \Pr[K_{m,i}(A)>32c^{1+m-i}x]\le e^{-x}\qquad(x\ge1). \tag{27}
--   $$
--
--   These conditional tail bounds are integrated over the ranks of $A$ in (29).
--
--   **Formalization Note** Probabilities and the expectation are taken under the explicit conditional law of Lemma 5.3; the expectation in (25) is a Lebesgue integral of the nonnegative count, stated together with its measurability.
--
--   Differences from the source:
--   - reading: conditioning on F_θ and r(A) (Lemma 5.3) → the measure `condLaw r₀ θ A rA` for every history r₀ at θ and every prescribed rA with values in [a, ∞) on A; reason: the explicit conditional law described in Lemma 5.3 and on p.18; holding for every history is the pointwise form of the conditional statement
--   - generalization: E[(K_{a,b}(A) choose k)] ≤ q^k → measurability of the binomial count, and its lower Lebesgue integral ≤ q^k; reason: the added measurability clause is true and makes the lower integral the expectation; dropping it gives (25)
--   - generalization: (27) for 0 ≤ i < m ≤ M → (27) for all 0 ≤ i < m; reason: the proof of (27) uses only i < m; the printed range is the case m ≤ M
--   - encoding: b ∈ (a, ∞], with 1 − e^{−(b−a)} → 1 as b → ∞ → b : WithTop ℝ, and the factor is 1 at b = ⊤; reason: extended reals; same instances
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Lemma 6.1, eqs. (24)–(27), p.23 (PDF p.25)

import Mathlib
import Definitions.Def_RGMISFast_Gamma
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Lemma 6.1 (Conditional growth and boundary bounds; Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), p.23): under the conditioning and
prescribed ranks of Lemma 5.3, let `a < b` and `q = e(1 − e^{−(b−a)})/(a − θ)` (with
`1 − e^{−(b−a)} → 1` as `b → ∞`). For every integer `k ≥ 1`, `Pr[|Γ_{a,b}(A)| ≥ k] ≤ q^k` (24)
and `E[(K_{a,b}(A) choose k)] ≤ q^k` (25). In particular, for `θ = a/2` and `c = 1 + 1/(2e²)`,
`Pr[|Γ_{a,ca}(A)| > x] ≤ e^{−x}` for `x ≥ 0` (26), and with `θ = a/2`, `a = a_m`, `b = b_i`,
`0 ≤ i < m`, `Pr[K_{m,i}(A) > 32c^{1+m−i}x] ≤ e^{−x}` for `x ≥ 1` (27).

**Formalization Note** The conditioning of Lemma 5.3 is the explicit law `condLaw r₀ θ A rA`, for
every history `r₀` at time `θ` (`0 ≤ θ < a`), every nonempty `A` connected in `G_θ` (computed from
the history) and every prescribed rank vector `rA` with values in `[a, ∞)` on `A`. `b ∈ (a, ∞]`
lies in `WithTop ℝ` (`b = ⊤` allowed). The expectation in (25) is the lower Lebesgue integral plus
a measurability clause. In (27) the source's range `0 ≤ i < m ≤ M` is widened to all `i < m`. -/
theorem lemma_6_1 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (θ a : ℝ) (hθ : 0 ≤ θ) (hθa : θ < a) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ θ) (A : Finset V) (hA : IsConnectedSet G A)
    (hAθ : ActiveAt G r₀ θ A) (rA : V → ℝ) (hrA : ∀ v ∈ A, a ≤ rA v) (bb : WithTop ℝ)
    (hab : ((a : ℝ) : WithTop ℝ) < bb) :
    (∀ k : ℕ, 1 ≤ k →
      condLaw r₀ θ A rA {r | k ≤ (GammaAB G r a bb A).card} ≤
        ENNReal.ofReal ((Real.exp 1 * oneMinusExp a bb / (a - θ)) ^ k)) ∧
    (∀ k : ℕ, 1 ≤ k →
      Measurable (fun r : V → ℝ => (KAB G r a bb A).choose k) ∧
      ∫⁻ r, ((KAB G r a bb A).choose k : ℝ≥0∞) ∂(condLaw r₀ θ A rA) ≤
        ENNReal.ofReal ((Real.exp 1 * oneMinusExp a bb / (a - θ)) ^ k)) ∧
    (θ = a / 2 → ∀ x : ℝ, 0 ≤ x →
      condLaw r₀ θ A rA {r | x < ((GammaAB G r a ((c * a : ℝ) : WithTop ℝ) A).card : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-x))) ∧
    (∀ m i : ℕ, i < m → θ = a / 2 → a = am m → ∀ x : ℝ, 1 ≤ x →
      condLaw r₀ θ A rA {r | 32 * c ^ (1 + m - i) * x < (Kmi G r m i A : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-x))) := by sorry

end RGMISFast
