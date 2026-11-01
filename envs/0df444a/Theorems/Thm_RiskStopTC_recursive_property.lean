-- Prove2me | Theorems.Thm_RiskStopTC_recursive_property
-- name    : RiskStopTC.recursive_property
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:35:12.45399+00:00
-- url     : https://prove2.me/theorems/d03b3987-9100-4d48-9b31-d904345e53a3
-- title:
--   p.20 — the recursive property $\rho_{0,T}(Z_\tau)=\rho_{0,m}(\rho_{m,T}(Z_\tau))$
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space with a filtration $\mathcal F_0\subset\cdots\subset\mathcal F_T$, $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathcal F_T=\mathcal F$, and $\mathcal Z_t=L^p(\Omega,\mathcal F_t,P)$ for a fixed $p\in[1,\infty]$. Relations between random variables hold $P$-almost surely.
--
--   For any one-step mappings $\varrho_t$ and nested functionals $\rho_{s,t}$ of (5.1) (with $\rho_{t,t}=\mathrm{id}$), and for $0\le s\le t\le u\le T$ and every random variable $X$,
--   $$\rho_{s,u}(X)=\rho_{s,t}\big(\rho_{t,u}(X)\big).$$
--   With $s=0$, $t=m$, $u=T$ and $X=Z_\tau$ this is the identity $\rho_{0,T}(Z_\tau)=\rho_{0,m}(\rho_{m,T}(Z_\tau))$, $m=1,\dots,T$, on p.20.
--
--   It reduces the time-$0$ objective of the stopping problem to the time-$m$ conditional one, which is how clauses (ii) and (iv) of Theorem 5.6 follow from (i).
--
--   Differences from the source:
--   - generalization: ρ_{0,T}(Z_τ) = ρ_{0,m}(ρ_{m,T}(Z_τ)), m = 1, …, T, for the mappings of Theorem 5.6 → ρ_{s,u}(X) = ρ_{s,t}(ρ_{t,u}(X)) for all s ≤ t ≤ u ≤ T, every function X and arbitrary ϱ; reason: the composition identity needs no axiom; s = 0, t = m, u = T, X = Z_τ gives the page's identity
--   - encoding: ρ_{s,t} for 0 ≤ s < t ≤ T, and ρ_{T,T}(Z_T) ≡ Z_T (footnote 10) → nested ϱ s t, with ρ_{t,t} = id for every t; reason: the paper fixes ρ_{T,T} = id; the identity at other diagonal indices is used only where the statement reads as the paper's at s = t
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, p.20 ("Note that by the recursive property (4.2) we have that ρ0,T(Zτ) = ρ0,m(ρm,T(Zτ)), m = 1, . . . , T")

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_RiskStopTC_nested

open MeasureTheory RiskFunctionals.NestedAVaR

namespace RiskStopTC

/-- **The recursive property of the nested functionals.** Pichler, Liu & Shapiro,
arXiv:1808.10807v3, p.20: "Note that by the recursive property (4.2) we have that
ρ0,T(Zτ) = ρ0,m(ρm,T(Zτ)), m = 1, . . . , T."

For `s ≤ t ≤ u ≤ T` and every `X`: `ρ_{s,u}(X) = ρ_{s,t}(ρ_{t,u}(X))`; with `s = 0`, `t = m`,
`u = T` and `X = Z_τ` this is the displayed identity.

**Formalization Note.** `ρ_{s,t} = nested ϱ s t` with `ρ_{t,t} = id`. The identity holds for
every function `X` and needs no axiom of the mappings. -/
theorem recursive_property {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (s t u : ℕ) (hst : s ≤ t) (htu : t ≤ u) (huT : u ≤ T)
    (X : Ω → ℝ) :
    nested ϱ s u X = nested ϱ s t (nested ϱ t u X) := by sorry

end RiskStopTC
