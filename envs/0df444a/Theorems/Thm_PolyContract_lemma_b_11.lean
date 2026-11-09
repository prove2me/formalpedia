-- Prove2me | Theorems.Thm_PolyContract_lemma_b_11
-- name    : PolyContract.lemma_b_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:51:59.049569+00:00
-- url     : https://prove2.me/theorems/77f5c2ea-7753-4721-aaca-4a3d82195ace
-- title:
--   Lemma B.11 — translation extensions
-- statement:
--   Let $g:2^E\to\mathbb R$ be submodular with $g(\emptyset)=0$, $m,\beta\in\mathbb R^E_{>0}$, $t:=m/\beta$, $(\mu_\alpha,\mu_\theta)\in\mathbb R^2$, $d_e:=(\mu_\theta-\mu_\alpha m_e)/\beta_e$, $K\in\mathbb R$, and $b\notin E$ a new element with $m_b,\beta_b>0$, $t_b:=m_b/\beta_b$. Define $g'(S):=g(S)$ and $g'(S\cup\{b\}):=g(S)+K-d(S)$ for $S\subseteq E$, with $F^{g'}$ taken with respect to $t,\beta^{-1}$ extended by $t_b,1/\beta_b$.
--
--   1. (a) If $d\ge0$, then $g'$ is submodular with $g'(\emptyset)=0$; if moreover $g$ is given by a cut form and $K,d$ are rational, then $g'$ is given by a cut form.
--   2. (b) For all $\alpha,\theta\in\mathbb R$ and $T\subseteq E$:
--   $$F^{g'}_{\alpha,\theta}(T)=F^g_{\alpha,\theta}(T),\qquad F^{g'}_{\alpha,\theta}(T\cup\{b\})=F^g_{\alpha-\mu_\alpha,\theta-\mu_\theta}(T)+K-\alpha t_b+\theta/\beta_b.$$
--   3. (c) $F^{g-d}_{\alpha,\theta}=F^g_{\alpha-\mu_\alpha,\theta-\mu_\theta}$ on $2^E$, and for every $\alpha$, $\xi^{g-d}(\alpha)=\xi^g(\alpha-\mu_\alpha)-d$, $\rho^{g-d}(\alpha)=\rho^g(\alpha-\mu_\alpha)+\mu_\theta$, and $A^{g-d}_\theta(\alpha)=A^g_{\theta-\mu_\theta}(\alpha-\mu_\alpha)$ for all $\theta$.
--
--   Parts (b) and (c) hold for every $(\mu_\alpha,\mu_\theta)\in\mathbb R^2$, without $d\ge0$. Subtracting a suitable modular function translates the full-plane best response along the share axis; this is the doubling step of the comb gadget.
--
--   Differences from the source:
--   - reading: ξ^{g−d}(α) = ξ^g(α − µα) − d, with ρ and A at these points → for every full-plane best response y of g at α − µα, y − d is a full-plane best response of g − d at α, with the stated marginals and level sets; reason: the full-plane best response is unique (§B.6.1, p.28), so this is the same statement
-- source:
--   Klimm, Lippke, Warode, The Complexity of Continuous Contract Design over Polymatroids, arXiv:2611.04934 (version of November 3, 2026, sha256 18cfc0a5…), Lemma B.11, p.33 (PDF p.34)

import Mathlib
import Definitions.Def_PolyContract_FullPlane
import Definitions.Def_PolyContract_CutForm

set_option autoImplicit false

namespace PolyContract

/-- **Lemma B.11** (Klimm, Lippke, Warode, arXiv:2611.04934, version of November 3, 2026, sha256
18cfc0a5…, p.33): translation extensions. Let `g : 2^E → ℝ` be submodular with `g(∅) = 0`,
`m, β ∈ ℝ^E_{>0}`, `t := m/β`, `(µ_α, µ_θ) ∈ ℝ²`, `d_e := (µ_θ − µ_α m_e)/β_e`, `K ∈ ℝ`, and `b ∉ E`
a new element with `m_b, β_b > 0` and `t_b := m_b/β_b`. Define `g′(S) := g(S)` and
`g′(S ∪ {b}) := g(S) + K − d(S)` for `S ⊆ E`. With `F^{g′}` taken with respect to `t` and `β⁻¹`
extended by `t_b` and `1/β_b`:

(a) If `d ≥ 0`, then `g′` is submodular with `g′(∅) = 0`, and if `g` is given by a cut form and
`K` and `d` are rational, then `g′` is given by a cut form.
(b) For all `α, θ ∈ ℝ` and `T ⊆ E`: `F^{g′}_{α,θ}(T) = F^g_{α,θ}(T)` and
`F^{g′}_{α,θ}(T ∪ {b}) = F^g_{α−µ_α, θ−µ_θ}(T) + K − α t_b + θ/β_b`.
(c) `F^{g−d}_{α,θ} = F^g_{α−µ_α, θ−µ_θ}` on `2^E` for all `α, θ`, and for every `α ∈ ℝ`,
`ξ^{g−d}(α) = ξ^g(α − µ_α) − d` and `ρ^{g−d}(α) = ρ^g(α − µ_α) + µ_θ`; moreover
`A^{g−d}_θ(α) = A^g_{θ−µ_θ}(α − µ_α)` for all `α, θ`.
Parts (b) and (c) do not use `d ≥ 0`, so they hold for every `(µ_α, µ_θ) ∈ ℝ²`.

**Formalization Note** `b` is `none : Option ι`; `T` and `T ∪ {b}` are `T.map some` and
`insert none (T.map some)`. `F^g`, `ξ^g`, `ρ^g`, `A^g` are `Ffun`, `IsFullPlaneBR`, `marginal`,
`levelSet` of `⟨g, m, β⟩`. Since the full-plane best response is unique (App. B.6.1, p.28), (c)
is stated as: every full-plane best response `y` of `g` at `α − µ_α` gives the full-plane best
response `y − d` of `g − d` at `α`, with the stated marginals and level sets. -/
theorem lemma_b_11 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (g : Finset ι → ℝ) (m β : ι → ℝ) (hg : NonmonotoneSubmod.Shared.Submodular g)
    (hg0 : g ∅ = 0) (hm : ∀ e, 0 < m e) (hβ : ∀ e, 0 < β e) (μα μθ K mb βb : ℝ)
    (hmb : 0 < mb) (hβb : 0 < βb) :
    let d : ι → ℝ := fun e => (μθ - μα * m e) / β e
    let I : QuadInstance ι := ⟨g, m, β⟩
    let I' : QuadInstance (Option ι) :=
      ⟨translationExt g K d, fun o => o.elim mb m, fun o => o.elim βb β⟩
    let Id : QuadInstance ι := ⟨subModular g d, m, β⟩
    -- (a)
    ((∀ e, 0 ≤ d e) →
      NonmonotoneSubmod.Shared.Submodular (translationExt g K d) ∧ translationExt g K d ∅ = 0 ∧
      ∀ cf : CutForm ι, cf.IsValid → (∀ S, g S = (cf.cutFn S : ℝ)) →
        ∀ (K' : ℚ) (d' : ι → ℚ), K = (K' : ℝ) → (∀ e, d e = (d' e : ℝ)) →
          ∃ cf' : CutForm (Option ι), cf'.IsValid ∧
            ∀ S, translationExt g K d S = (cf'.cutFn S : ℝ)) ∧
    -- (b)
    (∀ (α θ : ℝ) (T : Finset ι),
      I'.Ffun α θ (T.map Function.Embedding.some) = I.Ffun α θ T ∧
      I'.Ffun α θ (insert none (T.map Function.Embedding.some)) =
        I.Ffun (α - μα) (θ - μθ) T + K - α * (mb / βb) + θ / βb) ∧
    -- (c)
    (∀ (α θ : ℝ) (S : Finset ι), Id.Ffun α θ S = I.Ffun (α - μα) (θ - μθ) S) ∧
    (∀ (α : ℝ) (y : ι → ℝ), I.IsFullPlaneBR (α - μα) y →
      Id.IsFullPlaneBR α (y - d) ∧
      (∀ e, Id.marginal α (y - d) e = I.marginal (α - μα) y e + μθ) ∧
      ∀ θ : ℝ, Id.levelSet α (y - d) θ = I.levelSet (α - μα) y (θ - μθ)) := by sorry

end PolyContract
