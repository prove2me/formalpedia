-- Prove2me | Theorems.Thm_RankingCertGap_Supplement_theorem_4
-- name    : RankingCertGap.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:57:40.476362+00:00
-- url     : https://prove2.me/theorems/8fdd450c-54e3-473a-ae7d-6051e787b344
-- title:
--   Theorem 4 — exact online-degree-one characterization and unique optimizer
-- statement:
--   For every $f\in\mathcal F$,
--   $$
--   \chi(f;1)=H_f(1)=\int_0^1 f(y)\,dy,\qquad
--   \Gamma(1)=\gamma(1)=1,qquad \Delta(1)=0.
--   $$
--   The unique optimizer for $\Gamma(1)$ is $f^\star_1\equiv1$.
--
--   This is the exact boundary case for instances of online degree at most one; it is not a statement about one-regular graphs.
--
--   **Formalization Note** Optimizer uniqueness is pointwise on $[0,1]$, the domain of the source profile.
--
--   Differences from the source:
--   - encoding: profiles on $[0,1]$ → total real functions with optimizer equality on $[0,1]$; reason: this is the published profile representation and changes no source value
-- source:
--   Xu, Certifying Capacity and Gaps of the Rank-Dependent Gain-Sharing Framework for Ranking, arXiv:2610.17545 (held file sha256 75896dd9…), Theorem 4, p.8, eqs. (16)–(17)

import Mathlib
import Definitions.Def_RankingCertGap_Supplement_Objects
import Definitions.Def_RankingCertGap_PowerFilter

set_option autoImplicit false

namespace RankingCertGap.Supplement

/-- **Theorem 4 (Online degree at most one).** Xu, arXiv:2610.17545 (held file sha256
75896dd9…), Theorem 4, p.8, eqs. (16)–(17). Every profile has inner value
`H_f(1) = ∫₀¹ f`; capacity and competitiveness are one, the gap is zero, and `f ≡ 1` is the
unique optimizer.

**Formalization Note.** This is the online-degree-at-most-one class, not the one-regular class.
Optimizer equality is on `[0,1]`, the domain of the source profile. -/
theorem theorem_4 :
    (∀ f : ℝ → ℝ, f ∈ classF →
      chiC f (onDegLE 1) = Hf f 1 ∧ Hf f 1 = Hf1 f) ∧
    GammaC classF (onDegLE 1) = 1 ∧
    gammaC (onDegLE 1) = 1 ∧
    gapC classF (onDegLE 1) = 0 ∧
    oneProfile ∈ classF ∧
    chiC oneProfile (onDegLE 1) = GammaC classF (onDegLE 1) ∧
    (∀ f : ℝ → ℝ, f ∈ classF →
      chiC f (onDegLE 1) = GammaC classF (onDegLE 1) →
      ∀ y ∈ Set.Icc (0 : ℝ) 1, f y = oneProfile y) := by sorry

end RankingCertGap.Supplement
