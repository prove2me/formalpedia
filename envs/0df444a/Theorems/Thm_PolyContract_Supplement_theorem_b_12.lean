-- Prove2me | Theorems.Thm_PolyContract_Supplement_theorem_b_12
-- name    : PolyContract.Supplement.theorem_b_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:04:52.920116+00:00
-- url     : https://prove2.me/theorems/2fe8e8f2-f2e3-4366-b2c7-942984d7b474
-- title:
--   Theorem B.12 — one-element extensions: $\rho^f\le\rho^h$, $\rho'_e=\mathrm{med}(\rho^f_e,\theta_b,\rho^h_e)$, and the equation for $\theta_b$
-- statement:
--   Let $f:2^E\to\mathbb R$ be submodular with $f(\emptyset)=0$ (not necessarily monotone), $m,\beta\in\mathbb R^E_{>0}$, $d\in\mathbb R^E_{\ge0}$, $K\in\mathbb R$, and $b\notin E$ with $m_b,\beta_b>0$. Let $h:=f-d$ and let $f'$ be the extension of $f$ by $b$,
--   $$f'(S):=f(S),\qquad f'(S\cup\{b\}):=f(S)+K-d(S)\qquad(S\subseteq E).$$
--   Fix $\alpha\in\mathbb R$ and let $\rho^f,\rho^h,\rho'$ be the full-plane marginals of $f,h,f'$ at $\alpha$ and $\theta_b:=\rho'_b$. Then:
--
--   1. $\rho^f_e\le\rho^h_e$ for every $e\in E$, and $\sum_{e\in E}(\rho^h_e-\rho^f_e)/\beta_e=d(E)$;
--   2. $\rho'_e=\operatorname{med}(\rho^f_e,\theta_b,\rho^h_e)$ for every $e\in E$;
--   3. $\theta_b$ is the unique solution $\theta$ of
--   $$\frac{\alpha m_b-\theta}{\beta_b}=K-d(E)+Y(\theta),\qquad Y(\theta):=\sum_{e\in E}\frac{\operatorname{clamp}(\theta-\rho^f_e,0,\rho^h_e-\rho^f_e)}{\beta_e},$$
--   and $Y(\theta)\in[0,d(E)]$ for every $\theta$.
--
--   This describes exactly what adding one element does to the full-plane best response, and it is the tool from which the comb gadget is built.
--
--   Differences from the source:
--   - encoding: f′, h, ρ^f, ρ^h, ρ′, θ_b → b = none : Option ι, f′ = translationExt f K d, h = subModular f d, marginals α m − β ξ at given full-plane best responses ξ^f, ξ^h, ξ′; reason: the full-plane best responses exist and are unique (published milestone)
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Theorem B.12, App. B.6.3, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_PolyContract_FullPlane
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_PolyContract_Supplement_med3

set_option autoImplicit false

namespace PolyContract.Supplement

/-- **Theorem B.12** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, App. B.6.3, p.35): let `f : 2^E → ℝ` be submodular with `f(∅) = 0`, `m, β ∈ ℝ^E_{>0}`,
`d ∈ ℝ^E_{≥0}`, `K ∈ ℝ`, `b ∉ E` with `m_b, β_b > 0`, `h := f − d`, and `f′` the extension of `f` by
`b`, `f′(S) := f(S)`, `f′(S ∪ {b}) := f(S) + K − d(S)`. Fix `α ∈ ℝ`, and let `ρ^f, ρ^h, ρ′, θ_b` be
the full-plane marginals at `α`. Then
(a) `ρ^f_e ≤ ρ^h_e` for every `e ∈ E`, and `Σ_{e ∈ E} (ρ^h_e − ρ^f_e)/β_e = d(E)`;
(b) `ρ′_e = med(ρ^f_e, θ_b, ρ^h_e)` for every `e ∈ E`;
(c) `θ_b` is the unique solution `θ` of `(αm_b − θ)/β_b = K − d(E) + Y(θ)` (B.10), where
`Y(θ) := Σ_{e ∈ E} clamp(θ − ρ^f_e, 0, ρ^h_e − ρ^f_e)/β_e ∈ [0, d(E)]`.

**Formalization Note** `b` is `none : Option ι`, `f′` is the published `translationExt f K d`, and
`h` is `subModular f d`; `m, β` extend to `b` by `m_b, β_b`. The full-plane best responses
`ξ^f(α), ξ^h(α), ξ′(α)` are given as hypotheses (they exist and are unique, published milestone
`PolyContract.fullPlane_existsUnique`), and the marginals are `α m − β ξ`. Membership `Y(θ) ∈ [0, d(E)]`
is asserted for every `θ`. -/
theorem theorem_b_12 {ι : Type} [Fintype ι] [DecidableEq ι] (f : Finset ι → ℝ) (m β d : ι → ℝ)
    (K mb βb α : ℝ) (hf : NonmonotoneSubmod.Shared.Submodular f) (hf0 : f ∅ = 0)
    (hm : ∀ e, 0 < m e) (hβ : ∀ e, 0 < β e) (hd : ∀ e, 0 ≤ d e) (hmb : 0 < mb) (hβb : 0 < βb)
    (ξf ξh : ι → ℝ) (ξ' : Option ι → ℝ)
    (hξf : (⟨f, m, β⟩ : QuadInstance ι).IsFullPlaneBR α ξf)
    (hξh : (⟨subModular f d, m, β⟩ : QuadInstance ι).IsFullPlaneBR α ξh)
    (hξ' : (⟨translationExt f K d, fun o => o.elim mb m, fun o => o.elim βb β⟩ :
      QuadInstance (Option ι)).IsFullPlaneBR α ξ') :
    let ρf : ι → ℝ := fun e => α * m e - β e * ξf e
    let ρh : ι → ℝ := fun e => α * m e - β e * ξh e
    let ρ' : ι → ℝ := fun e => α * m e - β e * ξ' (some e)
    let θb : ℝ := α * mb - βb * ξ' none
    let Y : ℝ → ℝ := fun θ => ∑ e, clamp (θ - ρf e) 0 (ρh e - ρf e) / β e
    ((∀ e, ρf e ≤ ρh e) ∧ ∑ e, (ρh e - ρf e) / β e = ∑ e, d e) ∧
    (∀ e, ρ' e = med3 (ρf e) θb (ρh e)) ∧
    ((α * mb - θb) / βb = K - ∑ e, d e + Y θb ∧
      (∀ θ : ℝ, (α * mb - θ) / βb = K - ∑ e, d e + Y θ → θ = θb) ∧
      ∀ θ : ℝ, 0 ≤ Y θ ∧ Y θ ≤ ∑ e, d e) := by sorry

end PolyContract.Supplement
