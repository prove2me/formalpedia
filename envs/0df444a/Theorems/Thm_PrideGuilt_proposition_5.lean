-- Prove2me | Theorems.Thm_PrideGuilt_proposition_5
-- name    : PrideGuilt.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:00:14.0364+00:00
-- url     : https://prove2.me/theorems/4188fd74-cb10-47b6-b254-febe8be2c261
-- title:
--   Proposition 5 — in $\Omega_4$ the optimum $(p^*,f^*)$ induces the interior rate $\tau^*_m$ (corrected: demand $D\ge0$)
-- statement:
--   Assume the standing assumptions, $\gamma_P>0$, $\gamma_G>0$ and $(\gamma_P,\gamma_G)\in\Omega_4$, that is,
--
--   $$
--   \Big(2-\frac{b_1}{b_0}\Big)\gamma_G-\gamma_P<c_r-\Delta c<\gamma_P-\frac{b_1\gamma_G}{b_0}.
--   $$
--
--   Let
--
--   $$
--   p^*=\frac{1-b_1I_G}{2b_0}+\frac{c_n}{2}-\frac{(b_0\Delta c-b_0c_r+b_0\gamma_P+b_1\gamma_G)^2-4b_1^2\gamma_G^2}{8b_0^2(\gamma_P-\gamma_G)},\qquad f^*=\frac{b_0c_r+b_0\Delta c-b_1\gamma_G-b_0\gamma_P}{2b_0},
--   $$
--
--   and $\tau^*_m=\dfrac{b_0\Delta c-b_0c_r-b_1\gamma_G+b_0\gamma_P}{2b_0(\gamma_P-\gamma_G)}$. Then:
--
--   1. $D(p^*,f^*)\ge0$;
--   2. $\Pi(p^*,f^*)\ge\Pi(p,f)$ for every $(p,f)\in\mathbb R^2$ with $D(p,f)\ge0$;
--   3. $(p^*,f^*)$ is the only such pair attaining this value;
--   4. $c_r-\gamma_P<f^*<c_r-\gamma_G$, so $f^*$ falls in case (iv) of Lemma 1, and $\tau^*(f^*)=\tau^*_m$;
--   5. $0<\tau^*_m<1$, and $\tau^*_m$ is a stable equilibrium (Definition 1) at the reward $f^*$.
--
--   In $\Omega_4$ the manufacturer therefore optimally induces partial recycling.
--
--   Differences from the source:
--   - correction: the optimum of (5) (and Π⋆(f) = max_p Π(p,f)) is an unconstrained max over (p, f) → supremum over (p, f) ∈ ℝ² with demand D(p, f) ≥ 0; reason: as printed the max counts a negative demand times a negative margin as profit: it is +∞ for unrestricted f, and with b0 = 1, b1 = 0.5, cn = 1, cu = 0.5, ce = 3, IP = IG = 0, γP = 4, γG = 1 (a point of Ω4) the max over f ≤ c_r is 1.5625 at demand −1.25, independent of γG, contradicting Theorem 2(ii); the paper's footnote 4 (p.13) and p.12 require feasible demand
--   - reading: max over p, f with no stated domain → p and f range over all of ℝ; reason: (5) puts no bound on p or f; f* is negative at some points of Ω4 (−0.5 in the example above), so a sign restriction would falsify Proposition 5
--   - encoding: the manufacturer optimally sets p* and f*, which induces an interior ESE τ* = τ*_m → IsGreatest of the feasible profit set at (p*, f*), uniqueness of the maximizer, τ*(f*) = τ*_m ∈ (0, 1) with f* in the range of Lemma 1(iv), and τ*_m a stable equilibrium at f*; reason: spells out 'optimal' and 'interior ESE' with the paper's own objects
--   - encoding: τ*(f), the evolutionarily stable rate of Lemma 1 → the Lemma 1 formula tauStar, including its printed values at the endpoints and at τ^0 = τ_m(f); reason: the manufacturer's problem is built on the Lemma 1 formula (p.11); in Ω4 the endpoint values are the limits of τ_m, so the supremum does not depend on them
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Proposition 5, p.15

import Mathlib
import Definitions.Def_PrideGuilt_Standing
import Definitions.Def_PrideGuilt_IsStableEq
import Definitions.Def_PrideGuilt_profit
import Definitions.Def_PrideGuilt_InOmega4
import Definitions.Def_PrideGuilt_tauMStar
import Definitions.Def_PrideGuilt_fStar
import Definitions.Def_PrideGuilt_pStar

namespace PrideGuilt

/-- **Proposition 5 (the optimum in `Ω₄` induces an interior equilibrium), corrected: demand
`D ≥ 0`.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Proposition 5, p.15 (PDF 16).

Under the standing assumptions, with `γ_P, γ_G > 0` and `(γ_P, γ_G) ∈ Ω₄`, the pair `(p*, f*)` of
Proposition 5 has nonnegative demand, its profit is the greatest profit over all `(p, f) ∈ ℝ²`
with `D(p, f) ≥ 0`, it is the only such pair attaining it, and the reward `f*` induces the
interior equilibrium `τ*(f*) = τ*_m`: `c_r − γ_P < f* < c_r − γ_G` (case (iv) of Lemma 1),
`0 < τ*_m < 1`, and `τ*_m` is a stable equilibrium (Definition 1) at `f*`.

**Formalization Note.** "Optimally sets" is stated as `IsGreatest` of the feasible profit set with
uniqueness of the maximizer. `p, f` range over `ℝ` (`f*` can be negative in `Ω₄`). -/
theorem proposition_5 (P : Params) (hP : Standing P) (γP γG : ℝ) (hγP : 0 < γP) (hγG : 0 < γG)
    (hΩ : InOmega4 P γP γG) :
    0 ≤ demand P γP γG (pStar P γP γG) (fStar P γP γG) ∧
    IsGreatest {π : ℝ | ∃ p f : ℝ, 0 ≤ demand P γP γG p f ∧ π = profit P γP γG p f}
      (profit P γP γG (pStar P γP γG) (fStar P γP γG)) ∧
    (∀ p f : ℝ, 0 ≤ demand P γP γG p f →
        profit P γP γG p f = profit P γP γG (pStar P γP γG) (fStar P γP γG) →
        p = pStar P γP γG ∧ f = fStar P γP γG) ∧
    cr P - γP < fStar P γP γG ∧ fStar P γP γG < cr P - γG ∧
    tauStar P γP γG (fStar P γP γG) = tauMStar P γP γG ∧
    0 < tauMStar P γP γG ∧ tauMStar P γP γG < 1 ∧
    IsStableEq P γP γG (fStar P γP γG) (tauMStar P γP γG) := by sorry

end PrideGuilt
