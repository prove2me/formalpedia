-- Prove2me | Theorems.Thm_RiskStopTC_nested_properties
-- name    : RiskStopTC.nested_properties
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:35:39.622391+00:00
-- url     : https://prove2.me/theorems/a0518049-18ff-4844-b62f-11cb956e13cb
-- title:
--   Footnote 9, p.19 — the nested functionals $\rho_{s,t}$ are monotone and translation equivariant (and map $\mathcal Z_t$ to $\mathcal Z_s$, with (5.17))
-- statement:
--   Throughout, $(\Omega,\mathcal F,P)$ is a probability space with a filtration $\mathcal F_0\subset\cdots\subset\mathcal F_T$, $\mathcal F_0=\{\emptyset,\Omega\}$, $\mathcal F_T=\mathcal F$, and $\mathcal Z_t=L^p(\Omega,\mathcal F_t,P)$ for a fixed $p\in[1,\infty]$. Relations between random variables hold $P$-almost surely.
--
--   Let $\varrho_t$, $t<T$, be monotone, translation equivariant mappings $\mathcal Z_{t+1}\to\mathcal Z_t$ with (5.17), and let $\rho_{s,t}$ be the nested functionals (5.1). For $0\le s\le t\le T$:
--
--   1. $\rho_{s,t}$ maps $\mathcal Z_t$ into $\mathcal Z_s$;
--   2. $\rho_{s,t}$ is monotone: $X\preceq X'$ in $\mathcal Z_t$ implies $\rho_{s,t}(X)\preceq\rho_{s,t}(X')$;
--   3. $\rho_{s,t}$ is translation equivariant: $\rho_{s,t}(X+W)=\rho_{s,t}(X)+W$ for $X\in\mathcal Z_t$, $W\in\mathcal Z_s$;
--   4. $\rho_{s,t}$ has the local property: $\rho_{s,t}(\mathbb 1_AX)=\mathbb 1_A\rho_{s,t}(X)$ for $X\in\mathcal Z_t$, $A\in\mathcal F_s$.
--
--   The proof of Theorem 5.6 applies all four properties to the composed mappings $\rho_{m,T}$.
--
--   Differences from the source:
--   - generalization: the nested functionals are monotone and translation equivariant → also: ρ_{s,t} maps Z_t into Z_s and satisfies (5.17) for A ∈ F_s; reason: the proof of Theorem 5.6 uses both for ρ_{m,T} (p.21, 'by (5.17)'); dropping clauses 1 and 4 gives the footnote
--   - encoding: Z_t = L^p(Ω, F_t, P) as classes of a.e.-equal functions; ⪯ and = almost surely → functions Ω → ℝ with an F_t-measurable representative in L^p (IsLp (ℱ t) P p); relations ≤ᵐ[P] and =ᵐ[P]; reason: every class has such a representative; Lean convention; same instances
--   - encoding: monotone translation equivariant mappings ϱ_t|F_t : Z_{t+1} → Z_t with (5.17), t = 0, …, T − 1 → one family ϱ : ℕ → (Ω → ℝ) → Ω → ℝ with IsStoppingFamily (maps-to, monotone, translation equivariant, (5.17)) on IsLp (ℱ (t+1)) arguments, t < T; reason: values off Z_{t+1} and maps with t ≥ T are never used; monotonicity makes each ϱ_t respect a.e. equality, so it acts on classes; same instances
--   - encoding: ρ_{s,t} for 0 ≤ s < t ≤ T, and ρ_{T,T}(Z_T) ≡ Z_T (footnote 10) → nested ϱ s t, with ρ_{t,t} = id for every t; reason: the paper fixes ρ_{T,T} = id; the identity at other diagonal indices is used only where the statement reads as the paper's at s = t
-- source:
--   Pichler, Liu & Shapiro, Risk averse stochastic programming: time consistency and optimal stopping, arXiv:1808.10807v3, footnote 9, p.19

import Mathlib
import Definitions.Def_RiskFunctionals_NestedAVaR_Compositions
import Definitions.Def_MultiperiodRisk_Bellman_TestSet
import Definitions.Def_RiskStopTC_IsStoppingFamily
import Definitions.Def_RiskStopTC_nested

open MeasureTheory RiskFunctionals.NestedAVaR

namespace RiskStopTC

/-- **The nested functionals inherit the axioms.** Pichler, Liu & Shapiro, arXiv:1808.10807v3,
footnote 9, p.19: "Recall that the considered nested functionals are assumed to be monotone and
translation equivariant, while can be convex or concave."

For `s ≤ t ≤ T`, `ρ_{s,t} = nested ϱ s t`:
1. maps `Z_t` into `Z_s`;
2. is monotone on `Z_t`;
3. is translation equivariant: `ρ_{s,t}(X + W) = ρ_{s,t}(X) + W` for `X ∈ Z_t`, `W ∈ Z_s`;
4. has the local property (5.17): `ρ_{s,t}(1_A X) = 1_A ρ_{s,t}(X)` for `X ∈ Z_t`, `A ∈ F_s`.

**Formalization Note.** `ρ_{s,s}` is the identity. Clauses 1 and 4 are not in the footnote; the
proof of Theorem 5.6 uses them (p.21, "by (5.17)", applied to the composed mappings). -/
theorem nested_properties {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℕ mΩ) (P : Measure[mΩ] Ω)
    [IsProbabilityMeasure P] (p : ENNReal) (hp : 1 ≤ p) (T : ℕ) (hℱ : IsStandardFiltration ℱ T)
    (ϱ : ℕ → (Ω → ℝ) → Ω → ℝ) (hϱ : IsStoppingFamily ℱ P p T ϱ)
    (s t : ℕ) (hst : s ≤ t) (htT : t ≤ T) :
    (∀ X, IsLp (ℱ t) P p X → IsLp (ℱ s) P p (nested ϱ s t X)) ∧
      (∀ X X', IsLp (ℱ t) P p X → IsLp (ℱ t) P p X' → X ≤ᵐ[P] X' →
        nested ϱ s t X ≤ᵐ[P] nested ϱ s t X') ∧
      (∀ X W, IsLp (ℱ t) P p X → IsLp (ℱ s) P p W →
        nested ϱ s t (X + W) =ᵐ[P] nested ϱ s t X + W) ∧
      (∀ X, IsLp (ℱ t) P p X → ∀ A : Set Ω, MeasurableSet[ℱ s] A →
        nested ϱ s t (A.indicator X) =ᵐ[P] A.indicator (nested ϱ s t X)) := by sorry

end RiskStopTC
