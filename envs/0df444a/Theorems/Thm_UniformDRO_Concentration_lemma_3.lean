-- Prove2me | Theorems.Thm_UniformDRO_Concentration_lemma_3
-- name    : UniformDRO.Concentration.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:02:51.91095+00:00
-- url     : https://prove2.me/theorems/3b935365-04d7-4ed5-9b1e-e5e95403495a
-- title:
--   Lemma 3, p. 33 — the Cressie–Read conjugate f_k*(s) = (1/k)((k−1)s + 1)₊^{k*} − 1/k
-- statement:
--   Let $k>1$, $k_*=k/(k-1)$, and let $f_k$ be the Cressie–Read function, $f_k(t)=\frac{t^k-kt+k-1}{k(k-1)}$ for $t\ge0$ and $f_k(t)=+\infty$ for $t<0$. Its Fenchel conjugate $f_k^*(s)=\sup_t\{st-f_k(t)\}$ is, for every $s\in\mathbb R$,
--   $$
--   f_k^*(s)=\frac1k\big((k-1)s+1\big)_+^{k_*}-\frac1k .
--   $$
--
--   This closed form is the first step of the proof of Lemma 1: substituted into the general φ-divergence duality, it yields the one-dimensional dual (8).
--
--   **Formalization Note** The conjugate is the published `PhiDivRobust.Counterpart.conj`, an extended-real supremum over $t\ge0$ only; since $f_k=+\infty$ on $t<0$, this is the paper's supremum over all $t$. The function $f_k$ is passed as its real formula on $t\ge0$, coerced to `EReal`.
-- source:
--   Duchi & Namkoong, arXiv:1810.08750v6, Lemma 3, eq. (21), App. A.1, p. 33

import Mathlib
import Definitions.Def_PhiDivRobust_Counterpart_conj
import Definitions.Def_UniformDRO_Concentration_RobustRisk

namespace UniformDRO.Concentration

/-- Lemma 3 (Duchi & Namkoong, arXiv:1810.08750v6, App. A.1, p. 33, eq. (21)): for `k > 1`, the
Fenchel conjugate of the Cressie–Read function is
`f_k^*(s) = (1/k) ((k - 1) s + 1)_+^{k*} - 1/k`. The published `conj` takes the supremum over
`t ≥ 0`, which is the paper's `sup_t` because `f_k = +∞` on `t < 0`. -/
theorem lemma_3 (k : ℝ) (hk : 1 < k) (s : ℝ) :
    PhiDivRobust.Counterpart.conj (fun t => ((cressieRead k t : ℝ) : EReal)) s =
      ((1 / k * (max ((k - 1) * s + 1) 0) ^ kstar k - 1 / k : ℝ) : EReal) := by sorry

end UniformDRO.Concentration
