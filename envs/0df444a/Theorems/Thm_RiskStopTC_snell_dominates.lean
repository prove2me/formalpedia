-- Prove2me | Theorems.Thm_RiskStopTC_snell_dominates
-- name    : RiskStopTC.snell_dominates
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:35:25.857683+00:00
-- url     : https://prove2.me/theorems/9003fa97-d07f-4151-b195-f017c1edcf93
-- title:
--   §5.2.3, p.23 — the Snell envelope dominates $Z$ and is a $\mathfrak P$-supermartingale: $E_t\succeq Z_t$, $E_t\succeq\varrho_t(E_{t+1})$
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space with a filtration $\mathcal F_0\subset\cdots\subset\mathcal F_T$, $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathcal F_T=\mathcal F$, and $\mathcal Z_t=L^p(\Omega,\mathcal F_t,P)$ for a fixed $p\in[1,\infty]$. Relations between random variables hold $P$-almost surely.
--
--   Let $\varrho_t$, $t<T$, be monotone, translation equivariant mappings $\mathcal Z_{t+1}\to\mathcal Z_t$ with (5.17), let $Z_t\in\mathcal Z_t$, and let $E$ be the Snell envelope (5.14). Then
--
--   1. $E_t\in\mathcal Z_t$ and $E_t\succeq Z_t$ for $t=0,\dots,T$;
--   2. $E_t\succeq\varrho_{t|\mathcal F_t}(E_{t+1})$ for $t=0,\dots,T-1$, i.e. $(E_t)$ is a $\mathfrak P$-supermartingale in the sense of (5.24).
--
--   These are the two properties of $E$ used in the domination step (5.18) of the proof of Theorem 5.6.
--
--   Differences from the source:
--   - generalization: E_t ⪰ Z_t and E_t ⪰ ϱ_t(E_{t+1}) → also concludes E_t ∈ Z_t for t ≤ T; reason: Definition 5.5 treats E as a process in Z_{0,T}; dropping that conjunct gives the page's statement
--   - encoding: Z_t = L^p(Ω, F_t, P) as classes of a.e.-equal functions; ⪯ and = almost surely → functions Ω → ℝ with an F_t-measurable representative in L^p (IsLp (ℱ t) P p); relations ≤ᵐ[P] and =ᵐ[P]; reason: every class has such a representative; Lean convention; same instances
--   - encoding: monotone translation equivariant mappings ϱ_t|F_t : Z_{t+1} → Z_t with (5.17), t = 0, …, T − 1 → one family ϱ : ℕ → (Ω → ℝ) → Ω → ℝ with IsStoppingFamily (maps-to, monotone, translation equivariant, (5.17)) on IsLp (ℱ (t+1)) arguments, t < T; reason: values off Z_{t+1} and maps with t ≥ T are never used; monotonicity makes each ϱ_t respect a.e. equality, so it acts on classes; same instances
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, §5.2.3, p.23 ("It follows by the definition (5.14) that the Snell envelope sequence {Et}0≤t≤T is 𝔓-supermartingale. It also follows from (5.14) that Et ⪰ Zt"); (5.24), p.23

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_RiskStopTC_IsStoppingFamily
import Definitions.Def_RiskStopTC_snell

open MeasureTheory RiskFunctionals.NestedAVaR

namespace RiskStopTC

/-- **The Snell envelope dominates the reward and is a 𝔓-supermartingale.** Pichler, Liu &
Shapiro, arXiv:1808.10807v3, §5.2.3, p.23: "It follows by the definition (5.14) that the Snell
envelope sequence {Et}0≤t≤T is 𝔓-supermartingale. It also follows from (5.14) that Et ⪰ Zt, i.e.,
Et dominates Zt." (𝔓-supermartingale is (5.24): `X_t ⪰ ϱt|Ft(X_{t+1})`, `t = 0, …, T − 1`.)

For `t ≤ T`: `E_t ∈ Z_t` and `Z_t ⪯ E_t`; for `t < T`: `ϱ_t(E_{t+1}) ⪯ E_t`.

**Formalization Note.** `E` is `snell ϱ Z T`, defined by (5.14). `E_t ∈ Z_t` is the statement that
the recursion (5.14) stays in the spaces the paper's notation presumes. -/
theorem snell_dominates {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (hϱ : IsStoppingFamily ℱ P p T ϱ)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ t ≤ T, IsLp (ℱ t) P p (Z t)) :
    (∀ t ≤ T, IsLp (ℱ t) P p (snell ϱ Z T t) ∧ Z t ≤ᵐ[P] snell ϱ Z T t) ∧
      ∀ t < T, ϱ t (snell ϱ Z T (t + 1)) ≤ᵐ[P] snell ϱ Z T t := by sorry

end RiskStopTC
