-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_lemma_4_3
-- name    : SmallSecretLWE.Classical.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:27:20.661732+00:00
-- url     : https://prove2.me/theorems/2869a5c7-9012-46ff-bf1e-360f10dc839e
-- title:
--   Lemma 4.3 (= Lemma A.1) — two good walks with all singleton colors in a fixed set: probability $\le(350tT/\Delta)^{T/2}$
-- statement:
--   Let $G=(V,E,\Gamma)$ be a $t$-deficient edge-colored directed graph with average degree $\Delta=|E|/|V|$. Fix $w_0\in V$ and an avoidance set $B\subseteq[m]$ with $|B|\le 2T$. For independent $W_1,W_2\sim\mathrm{walk}^T_{w_0}$ let $\mathcal E$ be the event that $W_1$ and $W_2$ are good and $\mathrm{Single}(W_1\sqcup W_2)\subseteq B$. Then
--   $$\Pr[\mathcal E]\le\Big(\frac{350\,t\,T}{\Delta}\Big)^{T/2}.$$
--   It is what makes the vector $c$ of Construction 4.1 nontrivial (some $c_i=\pm1$).
--
--   Differences from the source:
--   - generalization: a directed graph $G=(V,E)$, $E\subseteq V\times V$ → a finite directed multigraph (edge occurrences `E` with `src`, `tgt`); degrees count occurrences; reason: a simple digraph is the case where $e\mapsto(\mathrm{src}\,e,\mathrm{tgt}\,e)$ is injective, so the statement specializes to the source's; the Kikuchi graph needs parallel edges
--   - encoding: $W\sim\mathrm{walk}^T_{w_0}$ (each step a uniform random out-neighbour) → `walkProb w₀ p` $=\prod_i 1/\text{out-deg}(w_i)$ on walks, $0$ otherwise; probabilities are finite sums over edge sequences; reason: same law; from a vertex with no out-edge the mass is lost (a sub-probability), which adds no hypothesis
--   - encoding: $(350tT/\Delta)^{T/2}$ → `Real.rpow`, `350 * t * T / G.avgDeg`; reason: same number; if $|E|=0$ Lean's quotient is $0$, and then no walk of length $T\ge1$ exists and the left side is $0$
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 17, Lemma 4.3; pp. 46–48, Lemma A.1 and proof

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Digraph

open scoped Classical

namespace SmallSecretLWE.Classical

/-- Lemma 4.3 (= Lemma A.1). Let `G` be a directed multigraph with a `t`-deficient edge coloring
`Γ : E → [m]` and average degree `Δ`. Fix `w_0` and `B ⊆ [m]` with `|B| ≤ 2T`. For independent
`W_1, W_2 ∼ walk^T_{w_0}`, the probability that both are good and `Single(W_1 ⊔ W_2) ⊆ B` is at
most `(350 t T / Δ)^{T/2}`. -/
theorem lemma_4_3 {V E : Type*} [Fintype V] [Fintype E] {m : ℕ} (G : MultiDigraph V E)
    (Γ : E → Fin m) (t : ℕ) (hΓ : G.IsDeficient Γ t) (w₀ : V) (T : ℕ) (B : Finset (Fin m))
    (hB : B.card ≤ 2 * T) :
    (∑ p₁ : Fin T → E, ∑ p₂ : Fin T → E,
      if G.IsGood w₀ p₁ ∧ G.IsGood w₀ p₂ ∧ single Γ (walkEdges p₁ + walkEdges p₂) ⊆ B then
        G.walkProb w₀ p₁ * G.walkProb w₀ p₂
      else 0) ≤
      (350 * t * T / G.avgDeg) ^ ((T : ℝ) / 2) := by sorry

end SmallSecretLWE.Classical
