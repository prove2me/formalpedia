-- Prove2me | Theorems.Thm_RiskFunctionals_Polyhedral_avar_polyhedral
-- name    : RiskFunctionals.Polyhedral.avar_polyhedral
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:54:42.311531+00:00
-- url     : https://prove2.me/theorems/86fc5ee5-4077-4add-8878-2a1bffe29f1f
-- title:
--   Example 2.70 — the average value-at-risk is a polyhedral acceptability functional
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $p\in[1,\infty)$, $q$ with $1/p+1/q=1$, and $\alpha\in(0,1]$. Take the parameters $k_0=1$, $k_1=2$, $w_0=1$, $c_0=1$, $c_1=(-1/\alpha,0)$, $w_1=(-1,1)$, $V_0=\mathbb R$, $V_1=\mathbb R^2_+$ in the single-period polyhedral functional
--   $$\mathcal R(Y)=\sup\Bigl\{v_0-\tfrac1\alpha\mathbb E[v_1^{(1)}]\ :\ v_0\in\mathbb R,\ v_1\in L_p(\mathcal F,\mathbb R^2_+),\ v_0-v_1^{(1)}+v_1^{(2)}=Y\Bigr\}.$$
--   Then:
--   1. $V_0$ and $V_1$ are non-empty polyhedral cones;
--   2. for every $Y\in L_p$, $\mathcal R(Y)$ is finite and
--   $$\mathbb{AV@R}_\alpha(Y):=\max_{x\in\mathbb R}\Bigl\{x-\tfrac1\alpha\mathbb E\bigl[(x-Y)^+\bigr]\Bigr\}=\mathcal R(Y),$$
--   the maximum being attained;
--   3. $\mathcal R$ is an acceptability functional on $L_p$;
--   4. complete recourse $\langle w_1,V_1\rangle=\mathbb R$ holds and $D=\{u:c_0-uw_0\in V_0^*,\ c_1-uw_1\in V_1^*\}=\{1\}$;
--   5. the dual set is $\mathcal Z_*=\{Z\in L_q:\ \mathbb E(Z)=1,\ 0\le Z\le1/\alpha\ \text{a.s.}\}$.
--
--   This is the book's model example of a polyhedral acceptability functional: the lower-tail average value-at-risk, written as a two-stage linear program with dual set the familiar box of densities.
--
--   **Formalization Note** The book prints $\mathbb E[(x-z)^-]$ and the constraint $v_1^{(1)}-v_1^{(2)}=z-v_0$; with its own convention $[a]^-=-\min(a,0)$ and its own parameters $w_0=1$, $w_1=(-1,1)$ these are sign slips for $\mathbb E[(x-Y)^+]=\mathbb E([Y-x]^-)$ (the form of (2.19)) and $v_1^{(1)}-v_1^{(2)}=v_0-Y$; the Lean uses the corrected signs. "Maximum" is rendered as `IsGreatest`, i.e. attained, exactly as printed; the attainment fails at $\alpha=1$ for $Y$ not essentially bounded above (finding F2), which the `_corrected` variant addresses. Finiteness is stated before the real part of $\mathcal R$ is used.
-- source:
--   Pflug & Römisch, Modeling, Measuring and Managing Risk, World Scientific 2007, p. 92, Example 2.70

import Mathlib
import Definitions.Def_RiskFunctionals_Polyhedral_Cones
import Definitions.Def_RiskFunctionals_Polyhedral_SinglePeriod

namespace RiskFunctionals.Polyhedral

open MeasureTheory

/-- Pflug & Römisch, *Modeling, Measuring and Managing Risk*, World Scientific 2007, p. 92,
Example 2.70, as printed (the maximum is claimed attained for every `α ∈ (0, 1]`). For `α ∈ (0, 1]` the average value-at-risk
`𝔸𝕍@ℝ_α(Y) = max_{x ∈ ℝ} {x − (1/α) 𝔼[(x − Y)⁺]}` is a polyhedral acceptability functional: with
the parameters `avarData α` (`k₀ = 1`, `k₁ = 2`, `w₀ = 1`, `c₀ = 1`, `c₁ = (−1/α, 0)`,
`w₁ = (−1, 1)`, `V₀ = ℝ`, `V₁ = ℝ²₊`) the functional (2.74) is finite on `L_p` and equals that
maximum, which is attained; it is an acceptability functional; complete recourse holds,
`D = {1}`, and the constraints of (2.76) are equivalent to `𝔼(Z) = 1` and `Z ∈ [0, 1/α]`.
(The page prints `(x − z)⁻` and `v₁⁽¹⁾ − v₁⁽²⁾ = z − v₀`; with its own `w₀ = 1`,
`w₁ = (−1, 1)` and (2.19) these read `(x − z)⁺` and `v₁⁽¹⁾ − v₁⁽²⁾ = v₀ − z`.) -/
theorem avar_polyhedral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (p q : ENNReal) (hp : 1 ≤ p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ = 1) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α ≤ 1) :
    (avarData α).IsPolyhedral ∧ IsPolyhedralCone (avarData α).V₀ ∧
    IsPolyhedralCone (avarData α).V₁ ∧
    (∀ Y : Ω → ℝ, MemLp Y p P →
      (avarData α).functional P p Y ≠ ⊥ ∧ (avarData α).functional P p Y ≠ ⊤ ∧
      IsGreatest {y : ℝ | ∃ x : ℝ, y = x - (1 / α) * ∫ ω, max (x - Y ω) 0 ∂P}
        ((avarData α).functional P p Y).toReal) ∧
    IsAcceptabilityFunctional P p (fun Y => ((avarData α).functional P p Y).toReal) ∧
    (avarData α).CompleteRecourse ∧
    (avarData α).dualFeasibleSet = {1} ∧
    (avarData α).dualSet P q =
      {Z : Ω → ℝ | MemLp Z q P ∧ ∫ ω, Z ω ∂P = 1 ∧
        ∀ᵐ ω ∂P, 0 ≤ Z ω ∧ Z ω ≤ 1 / α} := by sorry

end RiskFunctionals.Polyhedral
