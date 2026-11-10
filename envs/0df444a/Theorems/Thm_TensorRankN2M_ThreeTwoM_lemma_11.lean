-- Prove2me | Theorems.Thm_TensorRankN2M_ThreeTwoM_lemma_11
-- name    : TensorRankN2M.ThreeTwoM.lemma_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:16:17.859413+00:00
-- url     : https://prove2.me/theorems/1d4d1ba6-b0ab-4543-8777-f8a0b4dbf0fb
-- title:
--   Lemma 11 (Skew-augmentation rank bound) — rk(h) ≥ (d−1)/2 · rk(ℓ)
-- statement:
--   Let $V$ and $Y$ be vector spaces over a field $\mathbb F$ (any field, any dimension), $d$ a positive integer and $\ell:V^d\to Y$ a linear map. Let $V^{\wedge d}=\{c\in V^{d\times d}: c_{i,i}=0,\ c_{j,i}=-c_{i,j}\ \forall i,j\}$ and define the skew augmentation
--   $$h:V^{\wedge d}\to Y^d,\qquad h(c)=(\ell(c_{1,:}),\dots,\ell(c_{d,:})).$$
--   Then
--   $$\operatorname{rk}(h)\ \ge\ \frac{d-1}{2}\,\operatorname{rk}(\ell),$$
--   stated as $(d-1)\operatorname{rk}(\ell)\le 2\operatorname{rk}(h)$, where $\operatorname{rk}$ is the dimension (a cardinal) of the image.
--
--   Applied with $d=n-1$ to $\ell$ and $h$ of §4, it gives $\operatorname{rk}(H)\ge\frac{n-2}{2}\operatorname{rk}(L)$, the lower bound on $\operatorname{rk}(H)$ fed into Eq. (2).
--
--   Differences from the source:
--   - encoding: rk(h) ≥ (d−1)/2 · rk(ℓ) → ((d − 1 : ℕ) : Cardinal) * Module.rank 𝔽 (range ℓ) ≤ 2 * Module.rank 𝔽 (range h); reason: multiplying by 2 avoids division; Module.rank (a cardinal) needs no finite-dimensionality, which the source does not assume
--   - encoding: indices 1, …, d → Fin d (0-based); reason: Lean convention, same arrays
-- source:
--   Jason Yang, New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra, STOC 2027 submission (manuscript of October 2026, sha256 6c1df229…), p. 5, Lemma 11

import Mathlib
import Definitions.Def_TensorRankN2M_ThreeTwoM_SkewAugmentation

namespace TensorRankN2M.ThreeTwoM

/-- Lemma 11 (Skew-augmentation rank bound, p. 5): for vector spaces `V`, `Y` over any field, a
positive integer `d` and a linear map `ℓ : V^d → Y`, the skew augmentation
`h : V^{∧d} → Y^d`, `h(c) = (ℓ(c_{1,:}), …, ℓ(c_{d,:}))`, satisfies `rk(h) ≥ (d−1)/2 · rk(ℓ)`,
written `(d−1) · rk(ℓ) ≤ 2 · rk(h)` with ranks as cardinals. -/
theorem lemma_11 {𝔽 V Y : Type*} [Field 𝔽] [AddCommGroup V] [Module 𝔽 V] [AddCommGroup Y]
    [Module 𝔽 Y] (d : ℕ) (hd : 0 < d) (ℓ : (Fin d → V) →ₗ[𝔽] Y) :
    ((d - 1 : ℕ) : Cardinal) * Module.rank 𝔽 (LinearMap.range ℓ) ≤
      2 * Module.rank 𝔽 (LinearMap.range (skewAug ℓ)) := by sorry

end TensorRankN2M.ThreeTwoM
