-- Prove2me | Theorems.Thm_VertexSampleCSP_lemma_C_1
-- name    : VertexSampleCSP.lemma_C_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:25.692203+00:00
-- url     : https://prove2.me/theorems/c7a6472d-9222-4fe2-a4b1-2bfd6af310c6
-- title:
--   Lemma C.1, pp.15–16 — random sub-sums: $\mathbb E\,d_H(K,K_S)\le4\sqrt{(1-\rho)/\rho}\,\Lambda$, and $2\sqrt2\Lambda$, $4\sqrt{2(1-\rho)/\rho}\,\Lambda$
-- statement:
--   Let $Z_i=\mathrm{conv}\{c_{ia}:a\in[q]\}\subseteq\mathbb R^D$ for $i\in V$, $|V|=N$, let $\Lambda^2=\sum_{i,a}\|c_{ia}\|^2$, and for $S\subseteq V$ and $\rho>0$ let $K=\sum_iZ_i$ and $K_S=\rho^{-1}\sum_{i\in S}Z_i$.
--
--   1. If $S$ contains every $i$ independently with probability $\rho\in(0,1]$, then $\mathbb E\,d_H(K,K_S)\le4\sqrt{(1-\rho)/\rho}\,\Lambda$.
--   2. For $\rho=\tfrac12$ in that model, $\mathbb E\,d_H(K,K_S)\le2\sqrt2\,\Lambda$.
--   3. If $S$ is a uniformly random $N'$-subset of $V$ and $\rho=N'/N$, then
--
--   $$\mathbb E\,d_H(K,K_S)\le4\sqrt{2(1-\rho)/\rho}\,\Lambda.$$
--
--   The bounds are free of the dimension $D$. The third clause is the form used along the chain of samples in Theorem C.4(a).
--
--   **Formalization Note** With $q\ge1$ all the sets are nonempty and compact, so `Metric.hausdorffDist` is the paper's $d_H$.
--
--   Differences from the source:
--
--   - encoding: alphabet [q] = {1, …, q} → q ≥ 1 is a hypothesis and the alphabet is Fin q; reason: q = 0 leaves the optimum and the polytopes undefined, so this excludes only undefined cases
--   - encoding: ℝ^D → EuclideanSpace ℝ ι for a finite index type ι; reason: same spaces
--   - encoding: (b): ρ = N′/N with ρ > 0 → 1 ≤ N′ ≤ |V|; reason: this is the case the paper's ρ > 0 allows
--   - encoding: E over the random subset → the finite averages bernAvg and unifAvg; reason: same expectations
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma C.1, pp.15–16 (PDF pp.17–18)

import Mathlib
import Definitions.Def_VertexSampleCSP_bernAvg
import Definitions.Def_VertexSampleCSP_unifAvg
open scoped Pointwise

namespace VertexSampleCSP

/-- **Lemma C.1 (Random sub-sums).** Chang, *Optimal Vertex Sampling for Constraint Satisfaction
Problems*, STOC 2027 submission (manuscript sha256 1e0edd23…), Lemma C.1, pp.15–16 (PDF pp.17–18):
"Let Zi = conv{cia : a ∈ [q]} ⊆ ℝ^D for i ∈ V, |V| = N, let Λ² = Σ_{i,a}∥cia∥², and for S ⊆ V and
ρ > 0 let K = Σ_i Zi and KS = ρ^{−1} Σ_{i∈S} Zi.
(a) If S contains every i independently with probability ρ ∈ (0, 1], then
E dH(K, KS) ≤ 4√((1 − ρ)/ρ) Λ. For ρ = 1/2, E dH(K, KS) ≤ 2√2 Λ.
(b) If S is a uniformly random N′-subset of V and ρ = N′/N, then E dH(K, KS) ≤ 4√(2(1 − ρ)/ρ) Λ."

With `Z_i`, `Λ`, `K` and `K_S` as above:
1. for `ρ ∈ (0, 1]` and a Bernoulli(`ρ`) subset `S`: `E d_H(K, K_S) ≤ 4√((1 − ρ)/ρ) Λ`;
2. for `ρ = 1/2` and a Bernoulli(`1/2`) subset `S`: `E d_H(K, K_S) ≤ 2√2 Λ`;
3. for `1 ≤ N′ ≤ N`, `ρ = N′/N` and a uniformly random `N′`-subset `S`:
   `E d_H(K, K_S) ≤ 4√(2(1 − ρ)/ρ) Λ`.

**Formalization Note.** `ℝ^D` is `EuclideanSpace ℝ ι`; `[q]` is `Fin q` with `q ≥ 1`, so `K` and
every `K_S` are nonempty compact sets and `Metric.hausdorffDist` is the paper's `d_H`. The Minkowski
sums are `Finset.sum` of sets (the empty sum is `{0}`). In (b), `ρ > 0` is the condition `N′ ≥ 1`. -/
theorem lemma_C_1 {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] {q : ℕ} (hq : 0 < q)
    (c : V → Fin q → EuclideanSpace ℝ ι) :
    (∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      bernAvg ρ (fun S => Metric.hausdorffDist (∑ i, convexHull ℝ (Set.range (c i)))
          (ρ⁻¹ • ∑ i ∈ S, convexHull ℝ (Set.range (c i))))
        ≤ 4 * Real.sqrt ((1 - ρ) / ρ) * Real.sqrt (∑ i, ∑ a, ‖c i a‖ ^ 2)) ∧
    bernAvg (1 / 2 : ℝ) (fun S => Metric.hausdorffDist (∑ i, convexHull ℝ (Set.range (c i)))
          ((1 / 2 : ℝ)⁻¹ • ∑ i ∈ S, convexHull ℝ (Set.range (c i))))
        ≤ 2 * Real.sqrt 2 * Real.sqrt (∑ i, ∑ a, ‖c i a‖ ^ 2) ∧
    (∀ N' : ℕ, 1 ≤ N' → N' ≤ Fintype.card V →
      unifAvg N' (fun S => Metric.hausdorffDist (∑ i, convexHull ℝ (Set.range (c i)))
          (((N' : ℝ) / Fintype.card V)⁻¹ • ∑ i ∈ S, convexHull ℝ (Set.range (c i))))
        ≤ 4 * Real.sqrt (2 * (1 - (N' : ℝ) / Fintype.card V) / ((N' : ℝ) / Fintype.card V)) *
            Real.sqrt (∑ i, ∑ a, ‖c i a‖ ^ 2)) := by sorry

end VertexSampleCSP
