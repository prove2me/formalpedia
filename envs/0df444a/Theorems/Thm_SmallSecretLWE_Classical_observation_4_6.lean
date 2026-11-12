-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_observation_4_6
-- name    : SmallSecretLWE.Classical.observation_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:27:06.1382+00:00
-- url     : https://prove2.me/theorems/f0294e9c-a055-4867-8018-be7bba9f2bc8
-- title:
--   Observation 4.6 — when in-degree equals out-degree, $\nu$ is stationary for the random walk
-- statement:
--   Let $G=(V,E)$ be a directed graph with $\text{in-deg}(v)=\text{out-deg}(v)$ for every vertex $v$. If $w_0\sim\nu$ and $W=(w_0,\dots,w_T)\sim\mathrm{walk}^T_{w_0}$, then for every $1\le t\le T$ and every $v\in V$,
--   $$\Pr[w_t=v]=\nu(v)=\frac{\text{out-deg}(v)}{|E|}.$$
--
--   Differences from the source:
--   - generalization: a directed graph $G=(V,E)$, $E\subseteq V\times V$ → a finite directed multigraph (edge occurrences `E` with `src`, `tgt`); degrees count occurrences; reason: a simple digraph is the case where $e\mapsto(\mathrm{src}\,e,\mathrm{tgt}\,e)$ is injective, so the statement specializes to the source's; the Kikuchi graph needs parallel edges
--   - encoding: $W\sim\mathrm{walk}^T_{w_0}$ (each step a uniform random out-neighbour) → `walkProb w₀ p` $=\prod_i 1/\text{out-deg}(w_i)$ on walks, $0$ otherwise; probabilities are finite sums over edge sequences; reason: same law; from a vertex with no out-edge the mass is lost (a sub-probability), which adds no hypothesis
--   - encoding: $w_0\sim\nu$ (defined for $|E|>0$) → no hypothesis on $|E|$; with $|E|=0$ Lean's $\nu\equiv0$ and both sides are $0$; reason: only adds a degenerate case, where the identity holds trivially
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 15, Observation 4.6

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Digraph

open scoped Classical

namespace SmallSecretLWE.Classical

/-- Observation 4.6. In a directed multigraph with `in-deg(v) = out-deg(v)` for every vertex, if
`w_0 ∼ ν` and `W = (w_0, …, w_T) ∼ walk^T_{w_0}`, then for every `1 ≤ t ≤ T` the law of `w_t`
is `ν`. -/
theorem observation_4_6 {V E : Type*} [Fintype V] [Fintype E] (G : MultiDigraph V E)
    (hG : ∀ v, G.inDeg v = G.outDeg v) (T : ℕ) (t : Fin (T + 1)) (ht : 1 ≤ t.val) (v : V) :
    ∑ w₀, G.nu w₀ * ∑ p : Fin T → E, (if G.walkVtx w₀ p t = v then G.walkProb w₀ p else 0) =
      G.nu v := by sorry

end SmallSecretLWE.Classical
