-- Prove2me | Theorems.Thm_UCalibDirichlet_lemma_1_6
-- name    : UCalibDirichlet.lemma_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:16.509226+00:00
-- url     : https://prove2.me/theorems/1e7c7950-ba1e-4d89-aaaa-d757ce0ea913
-- title:
--   Lemma 1.6 — stability: $0\le\delta^i_F(a)\le W^i_F(a)/a_i$
-- statement:
--   Let $\ell_F$ be a proper loss with finite convex potential $F$. For every $i\in[K]$ and $a\in\mathbb R^K_{>0}$,
--   $$0\le\delta^i_F(a)\le\frac{W^i_F(a)}{a_i},\qquad W^i_F(a)=\|a\|_1\,\mathbb E_{R\sim\mathrm{Dir}(a_{-i})}\Big[\mathrm{Cov}_{X\sim\mathrm{Beta}(a_i,\|a_{-i}\|_1)}\big(f'_{i,R}(X),X\big)\Big].$$
--
--   The stability term of each round is thus controlled by a curvature of $F$ along the segment towards the observed label.
--
--   Differences from the source:
--   - encoding: proper loss ℓ_F : Δ_K × [K] → ℝ ∪ {+∞} with finite convex potential F → ℓ : (Fin K → ℝ) → Fin K → EReal with IsProperLoss ℓ and HasFiniteBayesRisk ℓ, F = bayesPot ℓ = −(Bayes risk); reason: the paper's ℓ_F is a proper loss whose potential F = −E_{i∼q}ℓ(q,i) is finite (footnote 1); EReal holds the value +∞; values off the simplex are irrelevant
--   - encoding: E_{P∼μ}[ℓ(P,i)] → expLoss ℓ μ i = eexp μ ℓ(·,i) = ∫⁻ ℓ(·,i)⁺ dμ − ∫⁻ ℓ(·,i)⁻ dμ in EReal; reason: the expectation of an extended-real random variable, keeping the value +∞; the negative part is bounded for a proper loss with finite Bayes risk (ℓ(p,i) ≥ ℓ(e_i,i) ∈ ℝ on Δ_K), so it is never ⊤ − ⊤
--   - encoding: W^i_F(a) via the covariance (11) → W valued in [0, +∞] via the symmetric form (12); δ in EReal; reason: (12) is the paper's equivalent form; it equals (11) whenever the covariance is finite and is +∞ otherwise, where the bound holds trivially
--   - encoding: K ≥ 1 → 2 ≤ K; reason: for K = 1, a_{−i} = 0 and Beta(a_i, 0) is undefined
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Lemma 1.6, display (11), p.5

import Mathlib
import Definitions.Def_UCalibDirichlet_IsProperLoss
import Definitions.Def_UCalibDirichlet_HasFiniteBayesRisk
import Definitions.Def_UCalibDirichlet_bayesPot
import Definitions.Def_UCalibDirichlet_delta
import Definitions.Def_UCalibDirichlet_W

namespace UCalibDirichlet

/-- **Lemma 1.6 (stability).** Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027
submission), Lemma 1.6, display (11), p.5: "For any `i ∈ [K]` and `a ∈ ℝ^K_{>0}`, we have
`0 ≤ δ^i_F(a) ≤ W^i_F(a)/a_i` where
`W^i_F(a) = ‖a‖₁ E_{R∼Dir(a_{−i})}[Cov_{X∼Beta(a_i,‖a_{−i}‖₁)}(f′_{i,R}(X), X)]`. (11)"

**Formalization Note.** `ℓ_F` is a proper loss with finite Bayes risk and `F = bayesPot ℓ`. `δ` is
the `EReal` difference `delta`; `W` is valued in `[0, +∞]` (symmetric form (12) of the
covariance), so the bound is trivially true when `W = +∞`. `K ≥ 2`: for `K = 1` the vector `a_{−i}`
is zero and `Beta(a_i, 0)` is undefined. -/
theorem lemma_1_6 {K : ℕ} (hK : 2 ≤ K) (ℓ : (Fin K → ℝ) → Fin K → EReal) (hℓ : IsProperLoss ℓ)
    (hfin : HasFiniteBayesRisk ℓ) (i : Fin K) (a : Fin K → ℝ) (ha : ∀ j, 0 < a j) :
    0 ≤ delta ℓ i a ∧ delta ℓ i a ≤ ((W (bayesPot ℓ) i a : ENNReal) : EReal) / (a i : EReal) := by sorry

end UCalibDirichlet
