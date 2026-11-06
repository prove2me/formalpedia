-- Prove2me | Theorems.Thm_SpinGirth5_theorem_3_potts
-- name    : SpinGirth5.theorem_3_potts
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:22.684175+00:00
-- url     : https://prove2.me/theorems/4e3840ba-2042-4490-a4cb-4cdec0c06ba3
-- title:
--   Theorem 3 — antiferromagnetic Potts model on girth-5 graphs: spectral gap $\delta/(8n)$ and mixing time $O_{\Delta,\delta,q,\beta}(n^2)$
-- statement:
--   For every $0<\delta<1$ there is $\Delta_0(\delta)>0$ such that the following holds. Let $\Delta\ge\Delta_0(\delta)$, $0\le\beta\le1$ and let $q\ge2$ be an integer with $q\ge(1+\delta)(1-\beta)\Delta$. Then there is $C=C(\Delta,\delta,q,\beta)>0$ such that for every $n$-vertex graph $G$ with maximum degree $\Delta$ and girth at least $5$, the heat-bath Glauber dynamics $P_{\mathrm{GD}}$ for the Potts distribution $\mu=\mu_{G,q,\beta}$
--
--   1. has spectral gap at least $\delta/(8n)$:
--   $$\frac{\delta}{8n}\langle f,f\rangle_\mu\le\langle f,(I-P_{\mathrm{GD}})f\rangle_\mu\quad\text{for all }f\perp\mathbf 1;$$
--   2. has mixing time $O_{\Delta,\delta,q,\beta}(n^2)$: for every $t\ge Cn^2$,
--   $$\max_{\sigma\in\operatorname{supp}\mu}\big\|P^t_{\mathrm{GD}}(\sigma,\cdot)-\mu\big\|_{\mathrm{TV}}\le\frac14 .$$
--
--   At $\beta=0$ the Potts distribution is uniform on proper colourings; Theorem 1 sharpens the mixing bound in that case.
--
--   **Formalization Note** The chain is the published `MarkovMixing.glauber µ` restricted to $\operatorname{supp}\mu$, the state space of the dynamics.
--
--   Differences from the source:
--   - generalization: spectral gap Ω_δ(1/n) → spectral gap at least δ/(8n); reason: p.34 proves the gap δ/(4(1+δ)n) ≥ δ/(8n), which is Ω_δ(1/n)
--   - encoding: mixing time O_{Δ,δ,q,β}(n²) → ∃ C(Δ, δ, q, β) > 0, chosen before the graph, with max_σ ‖P^t(σ,·) − µ‖_TV ≤ 1/4 for every t ≥ C n²; reason: t_mix(1/4) ≤ ⌈Cn²⌉ is equivalent since the worst-start distance is nonincreasing in t
--   - encoding: the heat-bath Glauber dynamics for µ_{G,q,β} → MarkovMixing.glauber µ restricted (subChain) to supp µ, with stationary law µ there; reason: the dynamics never leaves supp µ
--   - encoding: spectral gap at least γ → Poincaré inequality γ⟨f,f⟩_µ ≤ ⟨f, 𝓛 f⟩_µ for every f with E_µ f = 0; reason: the paper's own definition (§2.4, p.12)
--   - encoding: girth at least 5 (∞ for a forest) → 5 ≤ G.egirth; reason: Mathlib's egirth is ⊤ for acyclic graphs, so forests are included
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Theorem 3, p.4; proof in §6, pp.32–35 (gap δ/(4(1+δ)n) ≥ δ/(8n), p.34)

import Mathlib
import Definitions.Def_SpinGirth5_heatBath
import Definitions.Def_SpinGirth5_pottsDist
import Definitions.Def_mm_mixing

namespace SpinGirth5

/-- **Theorem 3** (antiferromagnetic Potts model). For every `0 < δ < 1` there is `Δ₀(δ) > 0` such
that, for every `n`-vertex graph with maximum degree `Δ ≥ Δ₀(δ)` and girth at least 5, every
`0 ≤ β ≤ 1` and every integer `q ≥ 2` with `q ≥ (1 + δ)(1 − β)Δ`, the heat-bath Glauber dynamics
for `μ_{G,q,β}`
* has spectral gap at least `δ/(8n)` (the paper's `Ω_δ(1/n)`), and
* has mixing time `O_{Δ,δ,q,β}(n²)`: there is `C = C(Δ, δ, q, β)` with
  `max_x ‖P^t(x, ·) − μ‖_TV ≤ 1/4` for every `t ≥ C n²`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Theorem 3, p.4; the gap `δ/(4(1+δ)n) ≥ δ/(8n)` is proved on p.34.

**Formalization Note** The chain is `MarkovMixing.glauber μ` restricted (`subChain`) to
`supp μ = {σ | μ σ > 0}`, which is its state space; its stationary law is `μ` on that set. The
spectral gap is the Poincaré inequality `γ ⟨f,f⟩_μ ≤ ⟨f, (I − P_GD) f⟩_μ` for `f ⊥ 1` (§2.4,
p.12). The mixing bound is stated through the worst-start distance `MarkovMixing.distStationary`
for every `t ≥ C n²`. `C` is chosen after `Δ, δ, q, β` and before the graph. Girth at least 5 is
`5 ≤ G.egirth`. -/
theorem theorem_3_potts (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ Δ₀ : ℕ, 0 < Δ₀ ∧ ∀ (Δ : ℕ) (β : ℝ) (q : ℕ), Δ₀ ≤ Δ → 0 ≤ β → β ≤ 1 → 2 ≤ q →
      (1 + δ) * (1 - β) * Δ ≤ q →
      ∃ C : ℝ, 0 < C ∧
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
          G.maxDegree = Δ → 5 ≤ G.egirth →
          PoincareIneq (pottsDist G q β)
            (fun f => f - (MarkovMixing.glauber (pottsDist G q β)).mulVec f)
            (δ / (8 * Fintype.card V)) ∧
          ∀ t : ℕ, C * (Fintype.card V : ℝ) ^ 2 ≤ t →
            MarkovMixing.distStationary
              (MarkovMixing.subChain (MarkovMixing.glauber (pottsDist G q β))
                (fun σ : V → Fin q => 0 < pottsDist G q β σ))
              (fun σ => pottsDist G q β σ.1) t ≤ 1 / 4 := by sorry

end SpinGirth5
