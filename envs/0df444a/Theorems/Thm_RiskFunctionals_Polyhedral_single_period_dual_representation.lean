-- Prove2me | Theorems.Thm_RiskFunctionals_Polyhedral_single_period_dual_representation
-- name    : RiskFunctionals.Polyhedral.single_period_dual_representation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:39.31865+00:00
-- url     : https://prove2.me/theorems/c8fdfaca-dd2f-4b4c-b79f-8a0de3c79e0e
-- title:
--   Proposition 2.68 — finiteness, concavity, continuity and dual representation of single-period polyhedral functionals
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $p\in[1,\infty)$, $q\in(1,\infty]$ with $1/p+1/q=1$, and let $\mathcal R$ be the polyhedral functional (2.74) on $\mathcal Y=L_p(\mathcal F,\mathbb R)$ with non-empty polyhedral $V_0,V_1$. Assume that $V_0$ and $V_1$ are polyhedral cones and
--
--   (i) $\langle w_1,V_1\rangle=\mathbb R$ (complete recourse),
--
--   (ii) $D:=\{u\in\mathbb R:c_0-uw_0\in V_0^*,\ c_1-uw_1\in V_1^*\}\neq\emptyset$ (dual feasibility).
--
--   Then
--   1. $\mathcal R$ is finite on $\mathcal Y$, concave and continuous on $\mathcal Y$;
--   2. for every $Y\in\mathcal Y$,
--   $$\mathcal R(Y)=\inf\{\mathbb E(YZ):Z\in\mathcal Z_*\},\qquad \mathcal Z_*=\{Z\in L_q(\mathcal F,\mathbb R):\ c_0-w_0\mathbb E(Z)\in V_0^*,\ c_1-w_1Z\in V_1^*\};$$
--   3. if $\mathcal Z_*\subseteq\{Z\in\mathcal Z:Z\ge0,\ \mathbb E(Z)=1\}$ (2.77), then $\mathcal R$ is an acceptability functional.
--
--   This is the single-period instance of the duality theory of polyhedral functionals: the dual set is cut out by finitely many linear conditions, read off from the program's data.
--
--   **Formalization Note** $\mathcal R$ is `EReal`-valued; finiteness is the first conclusion, and concavity, continuity and the acceptability properties are stated for its real part. The infimum is taken in `EReal`. The constraint $c_1-w_1Z\in V_1^*$ is required almost surely. The polyhedral cones are finite intersections of half-spaces through $0$, and $V^*$ is the book's polar $\{v^*:\langle v^*,v\rangle\le0\ \forall v\in V\}$.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, pp. 91–92, Proposition 2.68

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones
import Definitions.Def_RiskFunctionals_Polyhedral_SinglePeriod

namespace RiskFunctionals.Polyhedral

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 91–92,
Proposition 2.68. Let `𝒴 = L_p(ℱ, ℝ)`, `1 ≤ p < ∞`, `q ∈ (1, ∞]` with `1/p + 1/q = 1`, and let
`ℛ` be the polyhedral functional (2.74) with `V₀`, `V₁` polyhedral cones, complete recourse
(i) `⟨w₁, V₁⟩ = ℝ` and dual feasibility (ii) `D ≠ ∅`. Then `ℛ` is finite, concave and continuous
on `𝒴`; it has the dual representation (2.75) `ℛ(Y) = inf{𝔼(YZ) : Z ∈ 𝒵*}` with `𝒵*` of (2.76);
and if `𝒵* ⊆ {Z ∈ 𝒵 : Z ≥ 0, 𝔼(Z) = 1}` (2.77), then `ℛ` is an acceptability functional. -/
theorem single_period_dual_representation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ = 1) (D : SinglePeriodData) (hD : D.IsPolyhedral)
    (hV₀ : IsPolyhedralCone D.V₀) (hV₁ : IsPolyhedralCone D.V₁)
    (hi : D.CompleteRecourse) (hii : D.dualFeasibleSet.Nonempty) :
    (∀ Y : Ω → ℝ, MemLp Y p P → D.functional P p Y ≠ ⊥ ∧ D.functional P p Y ≠ ⊤) ∧
    ConcaveOnLp P p (fun Y => (D.functional P p Y).toReal) ∧
    ContinuousOnLp P p (fun Y => (D.functional P p Y).toReal) ∧
    (∀ Y : Ω → ℝ, MemLp Y p P →
      D.functional P p Y =
        sInf {x : EReal | ∃ Z ∈ D.dualSet P q, x = ((∫ ω, Y ω * Z ω ∂P : ℝ) : EReal)}) ∧
    (D.dualSet P q ⊆ {Z : Ω → ℝ | (∀ᵐ ω ∂P, 0 ≤ Z ω) ∧ ∫ ω, Z ω ∂P = 1} →
      IsAcceptabilityFunctional P p (fun Y => (D.functional P p Y).toReal)) := by sorry

end RiskFunctionals.Polyhedral
