-- Prove2me | Theorems.Thm_SecondBestBT_lemma_5_3
-- name    : SecondBestBT.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:45:34.319203+00:00
-- url     : https://prove2.me/theorems/da1d59b4-c0da-4f63-8dfb-97450fe3b545
-- title:
--   Lemma 5.3 — the normalized allocation level $G_b$ is increasing
-- statement:
--   Let $f_S$ be a seller prior on $\mathbb Z_{\ge0}$ with $f_S(0)>0$, let $F_S(u)=\sum_{k\le u}f_S(k)$, and let $G_b$ be the normalized allocation level of Eq. (6),
--   $$
--   G_b=\sum_{t=1}^{b}\frac{F_S(t-1)/F_S(0)}{t(1+\alpha)}\prod_{j=t+1}^{b}\Big(1-\frac{1}{j(1+\alpha)}\Big).
--   $$
--   For every $\alpha\ge0$:
--
--   1. $(G_b)_{b\ge1}$ is weakly increasing;
--   2. if $\alpha>0$, it is strictly increasing;
--   3. if $\alpha=0$, then for every $b\ge1$, $G_b<G_{b+1}$ exactly when $F_S(b)>F_S(0)$.
--
--   Differences from the source:
--   - generalization: $G_b$ of the seller prior of a threshold-stationary run (Section 5.1: a seller with $f_S(0)>0$, in the analysis full-support and $\alpha$-weakly regular) → every seller probability vector on $\mathbb N$ with $f_S(0)>0$; reason: Eq. (6) needs only $F_S(0)>0$; every seller of the paper's setting is an instance
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Lemma 5.3, p.19

import Mathlib
import Definitions.Def_SecondBestBT_Gnorm

namespace SecondBestBT

/-- **Lemma 5.3** (Liu–Qin–Ren–Wang, *Second-Best Bilateral Trade is 1/2 Efficient*,
arXiv:2606.03849, held version sha256 17184930…, Lemma 5.3, p.19). Let `f_S` be a seller prior on
`ℤ_{≥0}` with `f_S(0) > 0` and let `G_b` be the normalized allocation level (6) with
`F_S(t − 1)/F_S(0)` as cumulative ratios. For every `α ≥ 0`, `(G_b)_{b ≥ 1}` is weakly
increasing. If `α > 0`, it is strictly increasing. When `α = 0`, the step from `G_b` to
`G_{b+1}` is strict exactly when `F_S(b) > F_S(0)`.

**Formalization Note** `F_S(u) = ∑_{k ≤ u} f_S(k)` and `F_S(0) = f_S(0)`. -/
theorem lemma_5_3 (fS : ℕ → ℝ) (hnn : ∀ i, 0 ≤ fS i) (hsum : HasSum fS 1) (h0 : 0 < fS 0)
    (α : ℝ) (hα : 0 ≤ α) :
    MonotoneOn (Gnorm α (fun u => (∑ k ∈ Finset.range (u + 1), fS k) / fS 0)) (Set.Ici 1) ∧
    (0 < α →
      StrictMonoOn (Gnorm α (fun u => (∑ k ∈ Finset.range (u + 1), fS k) / fS 0)) (Set.Ici 1)) ∧
    (α = 0 → ∀ b : ℕ, 1 ≤ b →
      (Gnorm α (fun u => (∑ k ∈ Finset.range (u + 1), fS k) / fS 0) b <
          Gnorm α (fun u => (∑ k ∈ Finset.range (u + 1), fS k) / fS 0) (b + 1) ↔
        fS 0 < ∑ k ∈ Finset.range (b + 1), fS k)) := by sorry

end SecondBestBT
