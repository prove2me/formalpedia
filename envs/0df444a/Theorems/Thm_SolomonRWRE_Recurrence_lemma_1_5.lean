-- Prove2me | Theorems.Thm_SolomonRWRE_Recurrence_lemma_1_5
-- name    : SolomonRWRE.Recurrence.lemma_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:30:34.579689+00:00
-- url     : https://prove2.me/theorems/702f9a9a-9deb-4e16-9013-c36809cd1986
-- title:
--   Lemma (1.5) — in a fixed environment, Σ(ρ_{−n})⁻¹ and Σρ_n decide X_n → ∞, → −∞, or recurrence
-- statement:
--   Fix an environment $(a_n)_{n\in\mathbb Z}$ with $0<a_n<1$ for all $n$, with $\sigma_n=(1-a_n)/a_n$, $\rho_n=\sigma_1\cdots\sigma_n$ and $\rho_{-n}=\sigma_{-1}\cdots\sigma_{-n}$ for $n\ge1$, and let $(X_n)$ be the chain in this environment started at $0$. Then:
--
--   1. if $\sum_{n=1}^\infty(\rho_{-n})^{-1}=\infty$ and $\sum_{n=1}^\infty\rho_n<\infty$, then $\lim_{n\to\infty}X_n=\infty$ almost surely;
--   2. if $\sum_{n=1}^\infty(\rho_{-n})^{-1}<\infty$ and $\sum_{n=1}^\infty\rho_n=\infty$, then $\lim_{n\to\infty}X_n=-\infty$ almost surely;
--   3. if $\sum_{n=1}^\infty(\rho_{-n})^{-1}=\infty=\sum_{n=1}^\infty\rho_n$, then $\{X_n\}$ is recurrent; in fact
--   $$-\infty=\liminf_{n\to\infty}X_n<\limsup_{n\to\infty}X_n=\infty\quad\text{almost surely.}$$
--
--   This is the fixed-environment trichotomy which, combined with fluctuation theory (Lemma (1.6)) and Theorem (0.1), yields Theorem (1.7).
--
--   **Formalization Note** The series are in $[0,\infty]$. Recurrence is stated in the "in fact" form: the path goes below every level and above every level infinitely often.
-- source:
--   Solomon, Random Walks in a Random Environment, Ann. Probab. 3(1):1–31 (1975), DOI 10.1214/aop/1176996444, p. 3, Lemma (1.5)

import Mathlib
import Definitions.Def_SolomonRWRE_Recurrence_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SolomonRWRE.Recurrence

/-- Solomon, *Random Walks in a Random Environment*, Ann. Probab. 3(1) (1975), p. 3,
Lemma (1.5): for a fixed environment with `0 < a_n < 1` for all `n`, the chain `X` started at
`0` satisfies
(i) `Σ (ρ_{−n})⁻¹ = ∞`, `Σ ρ_n < ∞` imply `X_n → ∞` a.e.;
(ii) `Σ (ρ_{−n})⁻¹ < ∞`, `Σ ρ_n = ∞` imply `X_n → −∞` a.e.;
(iii) `Σ (ρ_{−n})⁻¹ = ∞ = Σ ρ_n` implies `{X_n}` is recurrent; in fact
`−∞ = lim inf X_n < lim sup X_n = ∞` a.e.

**Formalization Note.** The series run over `n ≥ 1` (Lean index `n + 1`) and are in `[0, ∞]`.
Recurrence is stated in the paper's "in fact" form (`Oscillates`). -/
theorem lemma_1_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℤ → ℝ) (ha : ∀ n, 0 < a n ∧ a n < 1)
    (X : ℕ → Ω → ℤ) (hX : IsChainInEnv P a 0 X) :
    (∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ = ∞ → ∑' n : ℕ, rho a ((n : ℤ) + 1) ≠ ∞ →
        ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atTop) ∧
    (∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ ≠ ∞ → ∑' n : ℕ, rho a ((n : ℤ) + 1) = ∞ →
        ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop atBot) ∧
    (∑' n : ℕ, (rho a (-((n : ℤ) + 1)))⁻¹ = ∞ → ∑' n : ℕ, rho a ((n : ℤ) + 1) = ∞ →
        ∀ᵐ ω ∂P, Oscillates (fun n => X n ω)) := by sorry

end SolomonRWRE.Recurrence
