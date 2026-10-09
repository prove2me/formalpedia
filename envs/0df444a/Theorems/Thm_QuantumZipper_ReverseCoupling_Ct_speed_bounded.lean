-- Prove2me | Theorems.Thm_QuantumZipper_ReverseCoupling_Ct_speed_bounded
-- name    : QuantumZipper.ReverseCoupling.Ct_speed_bounded
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:18:34.574837+00:00
-- url     : https://prove2.me/theorems/4688febc-3953-49e9-8b8a-cc78c019b081
-- title:
--   §4.1, p. 48 — |∂_t C_t(z)| is uniformly bounded for z in a compact subset of ℍ and all t
-- statement:
--   Let $C_t(z)=-\log\operatorname{Im}f_t(z)-\operatorname{Re}\log f'_t(z)$. For every compact set $K\subset\mathbb H$ there is a constant $M$ such that, for every continuous driving function $W$, every reverse Loewner flow $f_t$ driven by $W$, every $z\in K$ and every $t\ge0$, the map $t\mapsto C_t(z)$ is differentiable at $t$ (from the right at $t=0$) and
--   $$\Big|\frac{\partial}{\partial t}C_t(z)\Big|\le M .$$
--
--   Since $\mathfrak h_t(z)$ is a Brownian motion in the time parameter $-C_t(z)$, this bound shows that $\mathfrak h_t(z)$ is a Brownian motion stopped at a time at most a constant times $t$, hence a true martingale.
--
--   **Formalization Note** The paper's "for $z$ in the support of $\rho$" is a compact subset of $\mathbb H$, so the statement quantifies over all compact $K\subseteq\mathbb H$. The constant $M$ depends only on $K$; it is chosen before the driver, as the paper's use ("a constant times $t$") requires.
-- source:
--   Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, p. 48; C_t from the reverse-flow table, p. 46

import Mathlib
import Definitions.Def_QuantumZipper_ReverseCoupling_ZipperFields

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.ReverseCoupling

/-- **§4.1, p. 48** (unnumbered): "In the reverse case, the Loewner evolution gives that
`|∂/∂t C_t(z)|` is uniformly bounded above for `z` in the support of `ρ` and for all times `t`."
Sheffield, Conformal weldings of random surfaces, arXiv:1012.4797v2, §4.1, p. 48.

With `C_t(z) = −log Im f_t(z) − Re log f′_t(z)` (p. 46): for every compact `K ⊂ ℍ` there is a
constant `M` such that, for every continuous driving function `W`, every reverse Loewner flow driven
by `W`, every `z ∈ K` and every `t ≥ 0`, the map `t ↦ C_t(z)` is differentiable at `t` (right
derivative at `t = 0`) with derivative of absolute value at most `M`.

**Formalization Note** "The support of `ρ`" is a compact subset of `ℍ`; the statement quantifies
over all compact `K ⊆ ℍ`. The bound `M` is chosen before the driver, as the paper's use requires
(`𝔥_t(z)` is a Brownian motion run for a time "strictly less than a constant times `t`"). -/
theorem Ct_speed_bounded (K : Set ℂ) (hK : IsCompact K) (hKH : K ⊆ {z : ℂ | 0 < z.im}) :
    ∃ M : ℝ, ∀ (W : ℝ≥0 → ℝ), Continuous W → ∀ (g : ℝ≥0 → ℂ → ℂ), IsReverseLoewnerFlow W g →
      ∀ z ∈ K, ∀ t : ℝ≥0, ∃ c : ℝ,
        HasDerivWithinAt (fun s : ℝ => Cfun W g (Real.toNNReal s) z) c (Set.Ici 0) (t : ℝ) ∧
          |c| ≤ M := by sorry

end QuantumZipper.ReverseCoupling
