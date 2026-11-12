-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_lemma_4_2
-- name    : SmallSecretLWE.Classical.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:27:09.018203+00:00
-- url     : https://prove2.me/theorems/76b160ea-48d5-4da8-b206-e6ed24f76b22
-- title:
--   Lemma 4.2 — a random walk started from $\nu$ is good with probability $>1/4$
-- statement:
--   Let $G=(V,E)$ be a directed graph with at least one edge and $\text{in-deg}(v)=\text{out-deg}(v)$ for every vertex. If $w_0\sim\nu$ and $W\sim\mathrm{walk}^T_{w_0}$ with $T\ge1$, then
--   $$\Pr[W\text{ is good}]>\frac14 ,$$
--   where $W$ is good when fewer than $T/4$ of $w_0,\dots,w_{T-1}$ have out-degree below $3\Delta/16$, $\Delta=|E|/|V|$.
--
--   Differences from the source:
--   - generalization: a directed graph $G=(V,E)$, $E\subseteq V\times V$ → a finite directed multigraph (edge occurrences `E` with `src`, `tgt`); degrees count occurrences; reason: a simple digraph is the case where $e\mapsto(\mathrm{src}\,e,\mathrm{tgt}\,e)$ is injective, so the statement specializes to the source's; the Kikuchi graph needs parallel edges
--   - encoding: $W\sim\mathrm{walk}^T_{w_0}$ (each step a uniform random out-neighbour) → `walkProb w₀ p` $=\prod_i 1/\text{out-deg}(w_i)$ on walks, $0$ otherwise; probabilities are finite sums over edge sequences; reason: same law; from a vertex with no out-edge the mass is lost (a sub-probability), which adds no hypothesis
--   - encoding: $w_0\sim\nu$ → hypothesis $0<|E|$; reason: a nondegeneracy that only excludes the case where $\nu$ is undefined
--   - reading: walk length $T$ (range not stated) → hypothesis $1\le T$; reason: §4 works with the shortness parameter $T>0$ of Definition 2.2 (and Algorithm 1 requires $T\ge1$); at $T=0$ 'good' means $\mathrm{Bad}(W)<0$, which no walk satisfies
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 16, Lemma 4.2

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Digraph

open scoped Classical

namespace SmallSecretLWE.Classical

/-- Lemma 4.2. In a directed multigraph with at least one edge and `in-deg(v) = out-deg(v)` for
every vertex, if `w_0 ∼ ν` and `W ∼ walk^T_{w_0}` with `T ≥ 1`, then `Pr[W is good] > 1/4`. -/
theorem lemma_4_2 {V E : Type*} [Fintype V] [Fintype E] (G : MultiDigraph V E)
    (hG : ∀ v, G.inDeg v = G.outDeg v) (hE : 0 < Fintype.card E) (T : ℕ) (hT : 1 ≤ T) :
    1 / 4 < ∑ w₀, G.nu w₀ * ∑ p : Fin T → E, (if G.IsGood w₀ p then G.walkProb w₀ p else 0) := by sorry

end SmallSecretLWE.Classical
