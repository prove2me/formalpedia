-- Prove2me | Theorems.Thm_SpinGirth5_theorem_5_contraction_gap
-- name    : SpinGirth5.theorem_5_contraction_gap
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:40.149137+00:00
-- url     : https://prove2.me/theorems/65e3127c-c2b5-4bf3-b13b-4755457a244a
-- title:
--   Theorem 5 — local $(\alpha,\varepsilon)$-spectral contraction on girth-5 graphs gives Glauber spectral gap $\varepsilon/(4n)$
-- statement:
--   For every $0<\varepsilon\le1$ and every $\alpha\ge1$ there is $\Delta_0(\alpha,\varepsilon)\ge2\alpha$ such that the following holds. Let $G$ be an $n$-vertex graph with maximum degree $\Delta\ge\Delta_0(\alpha,\varepsilon)$ and girth at least $5$, let $q\ge2$, and let $(A,\lambda)$ be a multi-spin system ($A\in[0,1]^{q\times q}$ symmetric, $\lambda\in\mathbb R^q_{\ge0}$) whose Gibbs distribution $\mu=\mu_{G,A,\lambda}$ has irreducible Glauber dynamics and local $(\alpha,\varepsilon)$-spectral contraction (Condition 4). Then the discrete-time heat-bath Glauber dynamics $P_{\mathrm{GD}}=\frac1n\sum_vP_v$ with stationary measure $\mu$ has spectral gap at least $\varepsilon/(4n)$:
--   $$\frac{\varepsilon}{4n}\,\langle f,f\rangle_\mu\le\langle f,(I-P_{\mathrm{GD}})f\rangle_\mu\qquad\text{for all }f\perp\mathbf 1 .$$
--   This is the paper's general criterion; Theorem 3 and Theorem 1 follow by verifying Condition 4 for the Potts model.
--
--   **Formalization Note** $P_{\mathrm{GD}}$ is the published matrix `MarkovMixing.glauber µ`.
--
--   Differences from the source:
--   - encoding: spectral gap at least γ → Poincaré inequality γ⟨f,f⟩_µ ≤ ⟨f, 𝓛 f⟩_µ for every f with E_µ f = 0; reason: the paper's own definition (§2.4, p.12)
--   - encoding: µ = µ_{G,A,λ} has irreducible Glauber dynamics → the published Glauber chain of µ restricted to supp µ is irreducible, and Z > 0; reason: µ is a probability law only when Z > 0, and its Glauber dynamics lives on its support
--   - encoding: girth at least 5 (∞ for a forest) → 5 ≤ G.egirth; reason: Mathlib's egirth is ⊤ for acyclic graphs, so forests are included
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Theorem 5, p.5 (Condition 4, p.4; standing assumptions q ≥ 2 and A symmetric, §1.1, p.4)

import Mathlib
import Definitions.Def_SpinGirth5_gibbsWeight

namespace SpinGirth5

/-- **Theorem 5**. For every `0 < ε ≤ 1` and every `α ≥ 1` there is `Δ₀(α, ε) ≥ 2α` such that: for
every `n`-vertex graph `G` with maximum degree `Δ ≥ Δ₀(α, ε)` and girth at least 5, and every
spin system `A ∈ [0, 1]^{q×q}` (symmetric), `λ ∈ ℝ^q_{≥0}` such that `μ = μ_{G,A,λ}` has
irreducible Glauber dynamics and satisfies local `(α, ε)`-spectral contraction, the discrete-time
heat-bath Glauber dynamics with stationary measure `μ` has spectral gap at least `ε/(4n)`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Theorem 5, p.5 (Condition 4, p.4; standing assumptions `q ≥ 2`, `A`
symmetric, §1.1, p.4).

**Formalization Note** The discrete-time chain is `MarkovMixing.glauber μ` (its matrix acts on a
function `f` as `P_GD f = (1/n) ∑_v P_v f`), and "spectral gap at least `γ`" is the Poincaré
inequality `γ ⟨f, f⟩_μ ≤ ⟨f, (I − P_GD) f⟩_μ` for `f ⊥ 1` in `L²(μ)` (§2.4, p.12). Girth at least
5 is `5 ≤ G.egirth`; `Δ = G.maxDegree`. `Δ₀` is chosen after `α, ε` and before everything else.
The Gibbs measure is normalized, which needs `Z > 0`. -/
theorem theorem_5_contraction_gap (ε α : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hα : 1 ≤ α) :
    ∃ Δ₀ : ℝ, 2 * α ≤ Δ₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (q : ℕ) (S : Interaction q),
        2 ≤ q → Δ₀ ≤ G.maxDegree → 5 ≤ G.egirth → 0 < partitionFn G S →
        GlauberIrreducible (gibbsDist G S) → LocalSpectralContraction G S α ε →
        PoincareIneq (gibbsDist G S)
          (fun f => f - (MarkovMixing.glauber (gibbsDist G S)).mulVec f)
          (ε / (4 * Fintype.card V)) := by sorry

end SpinGirth5
