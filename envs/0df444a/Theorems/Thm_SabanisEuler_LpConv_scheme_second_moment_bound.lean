-- Prove2me | Theorems.Thm_SabanisEuler_LpConv_scheme_second_moment_bound
-- name    : SabanisEuler.LpConv.scheme_second_moment_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T00:12:43.320401+00:00
-- url     : https://prove2.me/theorems/1441741d-507a-4dd0-ac94-6d7ff34146d2
-- title:
--   Lemma 1 — uniform second-moment bound for the Euler-type scheme
-- statement:
--   Let $W$ be a $d_1$-dimensional Wiener martingale on a filtered probability space with right-continuous filtration, $T>0$, $p_0\ge2$, and let $b,\sigma$ and the sequences $b_n,\sigma_n$ be Borel measurable. Let the initial value $\xi$ be $\mathcal F_0$-measurable and let $(X_n)_{n\ge1}$ solve the numerical scheme (2.2) on $[0,T]$ with $X_n(0)=\xi$. Suppose A-5, B-2 with some $\alpha\in(0,1/2]$, and B-3 hold. Then
--   $$\sup_{n\ge1}\sup_{0\le u\le T}\mathbb E|X_n(u)|^2<\infty.$$
--
--   This is the $\mathcal L^2$-stability of the tamed-type explicit Euler schemes: the second moments of the approximations are bounded independently of the discretisation parameter $n$, even though the coefficients $b_n,\sigma_n$ themselves may grow like $n^\alpha$.
--
--   **Formalization Note** The paper writes the bound as "$<C$ for some $C:=C(T,K,\mathbb E[|X(0)|^2])$". Only the existence of a finite bound independent of $n$ is formalized, which is what the proof establishes (its constant also depends on the constant and exponent of B-2). Expectations and suprema are taken in $[0,\infty]$.
-- source:
--   Sabanis, Euler approximations with varying coefficients, arXiv:1308.1796v4, p. 7, Lemma 1, eq. (3.1)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_SabanisEuler_LpConv_Conditions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open SabanisEuler.Shared

namespace SabanisEuler.LpConv

open EthierKurtz

/-- Sabanis (2016), arXiv:1308.1796v4, p. 7, Lemma 1, eq. (3.1): under A-5, B-2 (with
`α ∈ (0, 1/2]`) and B-3, `sup_{n ≥ 1} sup_{0 ≤ u ≤ T} 𝔼|Xₙ(u)|² < ∞`.
The paper's dependence clause `C := C(T, K, 𝔼[|X(0)|²])` is not formalized: only a bound
independent of `n` is asserted (the proof also uses B-2's constant and `α`). -/
theorem scheme_second_moment_bound
    {d d₁ : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 mΩ) [ℱ.IsRightContinuous]
    (W : ℝ≥0 → Ω → SDEState d₁) (hW : IsWienerMartingale P ℱ W)
    (T : ℝ≥0) (hT : 0 < T)
    (p₀ : ℝ) (hp₀ : 2 ≤ p₀)
    (b : ℝ≥0 × SDEState d → SDEState d) (σ : ℝ≥0 × SDEState d → Diffusion d d₁)
    (hb : Measurable b) (hσ : Measurable σ)
    (bₙ : ℕ → ℝ≥0 × SDEState d → SDEState d) (σₙ : ℕ → ℝ≥0 × SDEState d → Diffusion d d₁)
    (hbₙ : ∀ n : ℕ, 1 ≤ n → Measurable (bₙ n)) (hσₙ : ∀ n : ℕ, 1 ≤ n → Measurable (σₙ n))
    (ξ : Ω → SDEState d) (hξ : Measurable[ℱ 0] ξ)
    (hA5 : CondA5 P p₀ ξ)
    (α : ℝ) (hα : 0 < α ∧ α ≤ 1 / 2)
    (hB2 : CondB2 T α b σ bₙ σₙ)
    (hB3 : CondB3 T p₀ bₙ σₙ)
    (Xₙ : ℕ → ℝ≥0 → Ω → SDEState d)
    (hXₙ : ∀ n : ℕ, 1 ≤ n → IsSchemeSolution P ℱ W T ξ bₙ σₙ n (Xₙ n)) :
    (⨆ n ∈ {n : ℕ | 1 ≤ n}, ⨆ u ∈ Set.Icc (0 : ℝ≥0) T,
      ∫⁻ ω, ‖Xₙ n u ω‖ₑ ^ (2 : ℝ) ∂P) < ⊤ := by sorry

end SabanisEuler.LpConv
