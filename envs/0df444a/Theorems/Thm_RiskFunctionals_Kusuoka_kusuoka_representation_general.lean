-- Prove2me | Theorems.Thm_RiskFunctionals_Kusuoka_kusuoka_representation_general
-- name    : RiskFunctionals.Kusuoka.kusuoka_representation_general
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:51:57.647698+00:00
-- url     : https://prove2.me/theorems/af098434-47a3-437c-8adb-d58742a6cc2b
-- title:
--   Theorem 2.45(iv) — the general representation with a penalty functional
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a non-atomic probability space, $1\le p<\infty$, $q$ the conjugate exponent, and $\mathcal A:L_p\to\mathbb R$ a version-independent acceptability functional (A1)–(A3) with dual representation $\mathcal A(Y)=\inf\{\mathbb E(YZ)-\bar A(Z): Z\in\mathcal Z_{\mathcal A}\}$, $\mathcal Z_{\mathcal A}\subseteq L_q$, where $(\bar A,\mathcal Z_{\mathcal A})$ is version-independent. No further condition is imposed. Then there are an index set $\mathcal G$, non-negative measures $m^{(1)}_G,m^{(2)}_G$ on $(0,1]$ and real numbers $\tilde A\{G\}$ for $G\in\mathcal G$, such that for every $Y\in L_p$
--   $$\mathcal A(Y)=\inf\Big\{\int_{(0,1]}\mathbb{AV@R}_\alpha(Y)\,dm^{(1)}_G(\alpha)-\int_{(0,1]}\mathbb{AV@R}_\alpha(-Y)\,dm^{(2)}_G(\alpha)-\tilde A\{G\} : G\in\mathcal G\Big\}.$$
--
--   This is the most general form of the Kusuoka-type representation in the book: the penalty $\tilde A$ carries the dual function $\bar A$ over to the index set.
--
--   **Formalization Note** The index set with its measures and functional is encoded as a set of triples $(m^{(1)}_G,m^{(2)}_G,\tilde A\{G\})$; this is the same as an indexed family together with a real functional on the index set. For every $Y$ and every triple both integrands are required to be integrable, so each integral is a finite number; the infimum is a greatest lower bound in $\mathbb R$ and the family is chosen before $Y$. The sign in front of the second integral is the one printed in the statement (the last display of the printed proof has $+$; FINDINGS F3).
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 60, Theorem 2.45(iv)

import Mathlib
import Definitions.Def_RiskFunctionals_Kusuoka_AverageValueAtRisk
import Definitions.Def_RiskFunctionals_Kusuoka_Functionals
open MeasureTheory ProbabilityTheory

namespace RiskFunctionals.Kusuoka

/-- Pflug & Römisch, p. 60, Theorem 2.45(iv), as printed: in general
`𝒜(Y) = inf {∫ 𝔸𝕍@ℝ_α(Y) dm⁽¹⁾_G(α) − ∫ 𝔸𝕍@ℝ_α(−Y) dm⁽²⁾_G(α) − Ã{G} : G ∈ 𝒢}` for
non-negative measures `m⁽¹⁾_G, m⁽²⁾_G` on `(0, 1]` and some real functional `Ã` on `𝒢`;
each element of `𝒢` is encoded as the triple `(m⁽¹⁾_G, m⁽²⁾_G, Ã{G})`. -/
theorem kusuoka_representation_general {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (hP : IsNonAtomic P)
    {p q : ENNReal} (hp1 : 1 ≤ p) (hp : p ≠ ⊤) (hpq : p.HolderConjugate q)
    (𝒜 : Lp ℝ p P → ℝ) (h𝒜 : IsAcceptabilityFunctional P 𝒜)
    (h𝒜vi : IsVersionIndependent P 𝒜)
    (𝒵𝒜 : Set (Lp ℝ q P)) (A : Lp ℝ q P → ℝ)
    (hrep : HasDualRepresentation P 𝒜 𝒵𝒜 A) (hAvi : IsVersionIndependentDual P 𝒵𝒜 A) :
    ∃ 𝒢 : Set (Measure ℝ × Measure ℝ × ℝ),
      (∀ m ∈ 𝒢, m.1 (Set.Ioc 0 1)ᶜ = 0 ∧ m.2.1 (Set.Ioc 0 1)ᶜ = 0) ∧
      ∀ Y : Lp ℝ p P,
        (∀ m ∈ 𝒢,
          Integrable (fun α => averageValueAtRisk P Y α) (m.1.restrict (Set.Ioc 0 1)) ∧
          Integrable (fun α => averageValueAtRisk P (fun ω => -Y ω) α)
            (m.2.1.restrict (Set.Ioc 0 1))) ∧
        IsGLB {x : ℝ | ∃ m ∈ 𝒢, x =
          (∫ α in Set.Ioc 0 1, averageValueAtRisk P Y α ∂m.1) -
            (∫ α in Set.Ioc 0 1, averageValueAtRisk P (fun ω => -Y ω) α ∂m.2.1) - m.2.2}
          (𝒜 Y) := by sorry

end RiskFunctionals.Kusuoka
