-- Prove2me | Theorems.Thm_QPSpinParisi_eq_3_28
-- name    : QPSpinParisi.eq_3_28
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:22:38.416664+00:00
-- url     : https://prove2.me/theorems/54c7f3ff-1da7-4b98-a501-688b3d7f3eb8
-- title:
--   Eq. (3.28) — $A_\xi$ is differentiable, with $A'_\xi(\beta)=\int_0^1\xi'(q)\gamma_{\xi,\beta}(q)\,dq$
-- statement:
--   The limiting free energy $A_\xi$ is differentiable at every $\beta>0$, and
--   $$A'_\xi(\beta)=\beta\Big\{\xi(1)-\int_0^1\xi(q)\,d\alpha_{\xi,\beta}(q)\Big\}=\beta\int_0^1\xi'(q)\alpha_{\xi,\beta}(q)\,dq=\int_0^1\xi'(q)\gamma_{\xi,\beta}(q)\,dq.\tag{3.28}$$
--   It holds for every mixture, finite or infinite. This is the identity that controls the mass of $\gamma_{\xi,\beta}$ as $\beta\to\infty$.
--
--   Differences from the source:
--   - generalization: one Brownian motion $B$ on an unnamed space → every `BrownianNoise`, on every probability space; reason: the source's $B$ is one such object, and `exists_noise` makes the statement non-vacuous
--   - generalization: $Y_n$ built as $\sum_pc_pY_{n,p}$ → every centered Gaussian field with covariance $n\xi(q(s,t))$ and continuous paths; reason: only the covariance is used; the source's field is one such field, and `exists_overlapField` makes the statement non-vacuous
--   - encoding: $\int_0^1\xi\,d\alpha$ → the integral on $(0,1]$ against the Stieltjes measure of $\alpha$; reason: a possible atom at $0$ does not matter, since $\xi(0)=0$
-- source:
--   Bhattacharya, Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Eq. (3.28), p.21 (PDF p.21)

import Mathlib
import Definitions.Def_QPSpinParisi_MixHyp
import Definitions.Def_QPSpinParisi_IsFreeEnergyLimit
import Definitions.Def_QPSpinParisi_IsMinB
import Definitions.Def_QPSpinParisi_alStieltjes
import Definitions.Def_QPSpinParisi_gamBeta
import Definitions.Def_QPSpinParisi_xiD
import Definitions.Def_QPSpinParisi_xiS
import Definitions.Def_QPSpinParisi_gamHat

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal Matrix

namespace QPSpinParisi

/-- Bhattacharya, *Parisi formula and product-state optimization of quantum mixed p-spin Hamiltonians*, manuscript (STOC 2027 submission; held version sha256 ae3fccd2…), Eq. (3.28), p.21, PDF p.21: `A_ξ` is differentiable, and
`A'_ξ(β) = β{ξ(1) - ∫₀¹ ξ(q) dα_{ξ,β}(q)} = β ∫₀¹ ξ'(q) α_{ξ,β}(q) dq = ∫₀¹ ξ'(q) γ_{ξ,β}(q) dq`. It holds for every mixture ("For an infinite
mixture, the same estimates are uniform under truncation", p.21).

**Formalization Note** `dα` is the Stieltjes measure of `α` on `(0, 1]`, which has the atom at `1`. A possible atom at `0` is harmless, since
`ξ(0) = 0`. -/
theorem eq_3_28 (c : ℕ → ℝ) (hc : MixHyp c) (W : BrownianNoise c) (A : ℝ → ℝ)
    (hA : IsFreeEnergyLimit c A) (β : ℝ) (hβ : 0 < β) (α : Icc (0 : ℝ) 1 → ℝ) (hα : IsMinB W β α) :
    HasDerivAt A (β * (xiS c 1 - ∫ q in Ioc (0 : ℝ) 1, xiS c q ∂(alStieltjes α hα.1).measure)) β ∧
    β * (xiS c 1 - ∫ q in Ioc (0 : ℝ) 1, xiS c q ∂(alStieltjes α hα.1).measure) =
      β * ∫ q in (0 : ℝ)..1, xiD c q * alHat α q ∧
    β * (∫ q in (0 : ℝ)..1, xiD c q * alHat α q) =
      ∫ q in (0 : ℝ)..1, xiD c q * gamHat (gamBeta β α) q := by sorry

end QPSpinParisi
