-- Prove2me | Theorems.Thm_SwitchOptStop_Boundary_theorem_3_8
-- name    : SwitchOptStop.Boundary.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:48.999572+00:00
-- url     : https://prove2.me/theorems/3757af0d-0e68-4d1a-95f1-aca8ed3ba3e2
-- title:
--   Theorem 3.8, p. 11 — the first entry time τ_D of the stopping region is optimal: V(ι, x) = E_{ι,x}∫₀^{τ_D} e^{−∫λ} H dt
-- statement:
--   Assume the setting of the mission with Assumptions 2.1, 2.2, 2.3 and $\underline H<0$. The set $C$ is the optimal continuation region and $D$ the optimal stopping region of (2.1): the first entry time $\tau_D$ of $D$ (2.6) is an optimal stopping time, i.e. for every $\iota$ and $x\in(0,\infty)^2$,
--   $$
--   V(\iota,x)=\mathsf E_{\iota,x}\int_0^{\tau_D}e^{-\int_0^t\lambda(\alpha_s)ds}H(\alpha_t,X_t)\,dt. \tag{3.10}
--   $$
--
--   This is the first main result of the paper: it holds although the cost need not be integrable over $[0,\infty)$, so the classical criterion does not apply.
--
--   **Formalization Note** Since $C$ and $D$ are defined from $V$, the first sentence of the theorem carries no content beyond (3.10). The conclusion includes that $\tau_D$ is a stopping time of the augmented filtration of $(\alpha,X)$; the expectation is the `EReal` cost. No Green-regularity hypothesis is added: the page's theorem has only Assumptions 2.1–2.3.
-- source:
--   Ernst & Mei, Exact optimal stopping for multidimensional linear switching diffusions, arXiv:2107.14441v1, p. 11, Theorem 3.8, (3.10)

import Mathlib
import Definitions.Def_SwitchOptStop_Boundary_Value

namespace SwitchOptStop.Boundary

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Theorem 3.8 (p. 11): the first entry time `τ_D` (2.6) of the stopping region is an optimal
stopping time for (2.1): `V(ι, x) = E_{ι,x} ∫₀^{τ_D} e^{−∫₀ᵗ λ(α_s) ds} H(α_t, X_t) dt` (3.10). -/
theorem theorem_3_8 (m : Model) (hQ : IsGenerator m) (h21 : Assumption21 m) (h22 : Assumption22 m)
    (hH : Hlow m < 0) {Ω : Type} [MeasurableSpace Ω] (S : Setting Ω) (hS : IsSetting m S)
    (h23 : Assumption23 S) :
    ∀ ι : Fin 2, ∀ x ∈ openQuadrant,
      IsStoppingTime (S.𝔾 x) (entryTime S x (stopSet m S)) ∧
      valueE m S ι x = costJ (Pι S ι) (costV m S x) (entryTime S x (stopSet m S)) := by sorry

end SwitchOptStop.Boundary
