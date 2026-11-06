-- Prove2me | Theorems.Thm_SpinGirth5_theorem_20_local_to_global
-- name    : SpinGirth5.theorem_20_local_to_global
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:12:07.20656+00:00
-- url     : https://prove2.me/theorems/b1100bb7-7c6a-468a-a584-ba032cf7cbb9
-- title:
--   Theorem 20 — local-to-global principle on girth-5 graphs: local weighted gaps $(1-\eta_v)/2$ give global gap $\varepsilon/2$
-- statement:
--   Let $G=(V,E)$ be a finite graph with girth at least $5$, and let $\mu$ be a distribution on $[q]^V$ that is conditionally independent ($X_u\perp\!\!\!\perp X_w\mid X_{V\setminus\{u,w\}}$ whenever $\operatorname{dist}_G(u,w)\ge2$) and whose Glauber dynamics is irreducible. Let $0\le\eta_v<1$ for $v\in V$ satisfy:
--
--   1. for every $v\in V$ and every feasible pinning $\tau$ outside $N[v]$, the weighted continuous-time Glauber dynamics for $\mu^\tau_{N[v]}$ with Laplacian $L_v+\frac{1+\eta_v}{2}L_{N(v)}$ (single-site Laplacians formed with respect to $\mu^\tau_{N[v]}$) has spectral gap at least $(1-\eta_v)/2$;
--   2. for some $\varepsilon>0$, $\sum_{u\in N(v)}\eta_u\le1-\varepsilon$ for every $v\in V$.
--
--   Then the continuous-time Glauber dynamics of $\mu$ has spectral gap at least $\varepsilon/2$:
--   $$\frac{\varepsilon}{2}\,\langle f,f\rangle_\mu\le\Big\langle f,\sum_{v\in V}L_vf\Big\rangle_\mu\qquad\text{for all }f\perp\mathbf 1 .$$
--   This is the local-to-global step of the paper: a global spectral gap follows from spectral gaps of weighted dynamics on stars $N[v]$.
--
--   Differences from the source:
--   - generalization: µ a conditionally independent Gibbs distribution on G → any distribution on [q]^V satisfying Definition 19; reason: the proof uses only Definition 19; every µ_{G,A,λ} satisfies it (p.21)
--   - encoding: feasible pinning τ outside N[v] and the measure µ^τ_{N[v]} on [q]^{N[v]} → a configuration x with µ(x) > 0 and the pinned law pin µ (N[v])ᶜ x on [q]^V; reason: restriction to N[v] is a bijection of supports preserving the inner product and the single-site Laplacians at sites of N[v]
--   - encoding: spectral gap at least γ → Poincaré inequality γ⟨f,f⟩_µ ≤ ⟨f, 𝓛 f⟩_µ for every f with E_µ f = 0; reason: the paper's own definition (§2.4, p.12)
--   - encoding: girth at least 5 (∞ for a forest) → 5 ≤ G.egirth; reason: Mathlib's egirth is ⊤ for acyclic graphs, so forests are included
-- source:
--   Chen, Liu, A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least Five, arXiv:2608.25491, Theorem 20, p.14 (Definitions 18–19, p.14)

import Mathlib
import Definitions.Def_SpinGirth5_heatBath

namespace SpinGirth5

open Finset

/-- **Theorem 20** (local-to-global principle). Let `G` have girth at least 5 and let `μ` be a
conditionally independent distribution on `[q]^V` whose Glauber dynamics is irreducible. Let
`0 ≤ η_v < 1` be such that
* for every `v` and every feasible pinning `τ` outside `N[v]`, the weighted continuous-time
  Glauber dynamics for `μ^τ_{N[v]}` with parameter `η_v`, whose Laplacian is
  `L_v + ((1 + η_v)/2) L_{N(v)}`, has spectral gap at least `(1 − η_v)/2`;
* `∑_{u∈N(v)} η_u ≤ 1 − ε` for every `v`, for some `ε > 0`.
Then the continuous-time Glauber dynamics for `μ` (Laplacian `L = ∑_v L_v`) has spectral gap at
least `ε/2`.

Chen, Liu, *A Spectral Local-to-Global Principle for Spin Systems on Graphs with Girth At Least
Five*, arXiv:2608.25491, Theorem 20, p.14 (with Definitions 18 and 19, p.14).

**Formalization Note** Girth at least 5 is `5 ≤ G.egirth` (forests have `egirth = ⊤`). A
feasible pinning outside `N[v]` is the restriction of a configuration `x` with `μ x > 0`, and
`μ^τ_{N[v]}` is `pin μ (N[v])ᶜ x`, kept on the full configuration space; its single-site
Laplacians at sites of `N[v]` are those of the paper's local measure. Spectral gaps are
Poincaré inequalities on `1⊥` (§2.4, p.12). -/
theorem theorem_20_local_to_global {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hgirth : 5 ≤ G.egirth)
    (μ : (V → Fin q) → ℝ) (hμ : MarkovMixing.IsDist μ) (hci : CondIndep G μ)
    (hirr : GlauberIrreducible μ) (η : V → ℝ) (hη0 : ∀ v, 0 ≤ η v) (hη1 : ∀ v, η v < 1)
    (hloc : ∀ (v : V) (x : V → Fin q), 0 < μ x →
      PoincareIneq (pin μ (closedNbhd G v)ᶜ x)
        (fun f y => singleLap (pin μ (closedNbhd G v)ᶜ x) v f y +
          (1 + η v) / 2 * lapSum (pin μ (closedNbhd G v)ᶜ x) (G.neighborFinset v) f y)
        ((1 - η v) / 2))
    (ε : ℝ) (hε : 0 < ε) (hsum : ∀ v, ∑ u ∈ G.neighborFinset v, η u ≤ 1 - ε) :
    PoincareIneq μ (lapSum μ univ) (ε / 2) := by sorry

end SpinGirth5
