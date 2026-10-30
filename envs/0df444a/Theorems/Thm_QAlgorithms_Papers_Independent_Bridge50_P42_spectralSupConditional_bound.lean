-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P42_spectralSupConditional_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P42.spectralSupConditional_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:05:25.705617+00:00
-- url     : https://prove2.me/theorems/d1e0b796-7d6d-4c10-bcd7-2eeb9e61db52
-- title:
--   Optimized spectral sup conditional information bound
-- statement:
--   Let $W(y,z\mid x)=W_1(y\mid x)W_2(z\mid y)$ be a fixed normalized degraded DMC on finite nonempty alphabets. For every positive $n$, choose an arbitrary probability law $P_{X^n}$, with no independence or consistency assumption. Use $W^n$ to induce $(X^n,Y^n,Z^n)$, and define, on actual joint support,
--
--   $$\imath_n(X^n;Y^n\mid Z^n)=\frac1n\log_2\frac{W_{Y^n\mid X^nZ^n}(Y^n\mid X^n,Z^n)}{P_{Y^n\mid Z^n}(Y^n\mid Z^n)}.$$
--
--   For a random-variable sequence $B_n$, its spectral supremum here is $\sup\{r:\liminf_n\Pr(B_n\le r)<1\}$, with extended-real extrema. Writing $\overline I(\mathbf X;\mathbf Y\mid\mathbf Z)=\operatorname{p\!\!-limsup}_n\imath_n$, one has
--
--   $$\sup_{\{P_{X^n}\}_{n\ge1}}\overline I(\mathbf X;\mathbf Y\mid\mathbf Z)\le C_s^{\mathrm{DM}}(W),$$
--
--   where $C_s^{\mathrm{DM}}(W)=\max_{P_X}[I(X;Y)-I(X;Z)]$. This is the stronger spectral-sup bound singled out in (65).
-- source:
--   Information Spectrum Approach to Strong Converse Theorems for Degraded Wiretap Channels, arXiv:1406.6758v2, PDF p. 8, §V-B, (65)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P42

open Filter

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

attribute [local instance] Classical.propDecidable

/-- PDF pp.8–9, (65): the optimized spectral SUP conditional-information rate
is bounded by the finite degraded DMC secrecy capacity. Optimization is over
all block input laws, including correlated and block-inconsistent inputs. -/
theorem spectralSupConditional_bound
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [Nonempty X] [Nonempty Y] [Nonempty Z] (W : DegradedDMC X Y Z) :
    sSup (Set.range (spectralConditionalSup W)) ≤ (secrecyCapacity W : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P42

end
