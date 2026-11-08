-- Prove2me | Theorems.Thm_RandMatDisc_lemma_3_4
-- name    : RandMatDisc.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:49:47.656264+00:00
-- url     : https://prove2.me/theorems/d7a11673-05af-4745-a8ba-1649720a8a31
-- title:
--   Lemma 3.4 — ball containment
-- statement:
--   Let $v_1,\dots,v_N\in\mathbb R^D$, $q\ge0$ and $t\ge0$. Suppose that for every $u\in\mathbb S^{D-1}$ there are at least $\lceil q\rceil$ indices $i\in[N]$ with $\langle u,v_i\rangle\ge t$. Then
--
--   $$qt\,B_2^D\subseteq K_q(v),$$
--
--   where $B_2^D$ is the closed Euclidean unit ball and $K_q(v)=\{\sum_ia_iv_i:0\le a_i\le1,\ \sum_ia_i\le q\}$.
--
--   Every vector of norm at most $qt$ is a fractional combination of the $v_i$ with total weight at most $q$; this is how the algorithm's comparison point cancels the residual.
--
--   Differences from the source:
--   - generalization: the threshold $t=\frac12\sqrt{\log\alpha_d}$ of (13) → every $t\ge0$; reason: the paper's $t$ is a square root, hence $\ge0$, and the proof uses nothing else about it
--   - encoding: $qt\,B_2^D$ → the closed ball of radius $qt$ about $0$; reason: same set since $qt\ge0$
-- source:
--   Kızıldağ, Li, Stable and Online Algorithms for Random Matrix Discrepancy, arXiv:2610.01591 (held file sha256 889af7fc…), Lemma 3.4, p.17 (PDF p.19), eqs. (18), (19)

import Definitions.Def_RandMatDisc_capCount

namespace RandMatDisc

/-- **Lemma 3.4 (Ball containment)**, Kızıldağ, Li, arXiv:2610.01591 (held file sha256
889af7fc…), p.17 (PDF p.19).

Let `v₁, …, v_N ∈ ℝᴰ`, `q ≥ 0` and `t ≥ 0`. Suppose that for every `u ∈ S^{D−1}` there are at
least `⌈q⌉` indices `i ∈ [N]` with `⟨u, vᵢ⟩ ≥ t`. Then `qt B₂ᴰ ⊆ K_q(v)` (19), where `B₂ᴰ` is the
closed unit ball and `K_q(v)` is (18).

**Formalization Note.** `qt B₂ᴰ` is the closed ball of radius `qt` about `0` (`qt ≥ 0`). The
paper's `t` is `½√(log α_d) ≥ 0`; the lemma is stated for every `t ≥ 0`. `q ≥ 0` is the range
on which (18) defines `K_q`. -/
theorem lemma_3_4 {D N : ℕ} (v : Fin N → EuclideanSpace ℝ (Fin D)) (t q : ℝ) (ht : 0 ≤ t)
    (hq : 0 ≤ q) (hcap : ∀ u : EuclideanSpace ℝ (Fin D), ‖u‖ = 1 → ⌈q⌉₊ ≤ capCount u v t) :
    Metric.closedBall (0 : EuclideanSpace ℝ (Fin D)) (q * t) ⊆ Kq v q := by sorry

end RandMatDisc
