-- Prove2me | Theorems.Thm_SumReLU_lemma_4_2
-- name    : SumReLU.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:47.616216+00:00
-- url     : https://prove2.me/theorems/062ff267-a5fe-44df-8854-dba3b2646b35
-- title:
--   Lemma 4.2 — under the probing events, the top eigenvector of any $(\sqrt\xi/3)$-perturbation of $M_{2p+2}(u)$ has $|\hat r_1\cdot w_{i^*}|\ge0.99$
-- statement:
--   Let $\xi\in(0,1/300]$, let $w_1,\dots,w_k\in\mathbb R^d$ be unit vectors and $\beta_i\in[0,1]$, let $\lambda\in(0,\sqrt\xi/10]$ and $p=\lceil\log(k/\lambda)/\log(1+\xi)\rceil$. Let $i^*$ satisfy $\beta_{i^*}\ge\lambda$, let $Z>0$, and let $u\in\mathbb C^d$ lie in both events (11):
--   $$
--   |w_{i^*}\cdot u|\ge Z^{1/(2p)},\qquad |w_{i^*}\cdot u|\ge(1+\xi)|w_j\cdot u|\ \text{ for all } j \text{ with } |w_j\cdot w_{i^*}|\le1-\xi .
--   $$
--   Let $M_{2p+2}(u)=Z^{-1}\sum_i\beta_i|w_i\cdot u|^{2p}w_iw_i^\top$ and let $\widehat M$ be any real symmetric matrix with $\|\widehat M-M_{2p+2}(u)\|_2\le(\sqrt\xi/3)\|M_{2p+2}(u)\|_2$. Then every top eigenvector $\hat r_1$ of $\widehat M$ satisfies
--   $$
--   |\hat r_1\cdot w_{i^*}|\ge0.99 .
--   $$
--
--   This reduces coarse direction recovery to estimating the filtered matrix to constant relative spectral accuracy at a probe in the two events.
--
--   Differences from the source:
--   - generalization: $\lambda\in(0,\sqrt\xi/10]$ "be less than a sufficiently small constant" → every $\lambda\in(0,\sqrt\xi/10]$; reason: the perturbation argument closes for every such $\lambda$ (with $\xi\le1/300$ the error ratio is at most $0.109$, giving $|\hat r_1\cdot w_{i^*}|\ge0.992$); the statement implies the printed one for any smaller threshold
--   - generalization: $u$ drawn and fixed from $\mathcal U$, $Z=Z_p(\mathcal U)$ → every $u\in\mathbb C^d$ in the two events and every $Z>0$; reason: the proof uses only the events (11) and $Z>0$; it specializes to every $\mathcal U$
--   - reading: "the top eigenvector $\hat r_1$" → every unit eigenvector of the largest eigenvalue (`IsTopEigenvector`); reason: "the" is ambiguous when $\lambda_1(\widehat M)$ is not simple; the universal reading is the stronger one
--   - encoding: $M_{2p+2}(u)$ defined in (M), $\|\cdot\|_2$ → form (ii) of (M) (`filterMatrix`) and the operator norm on Euclidean $\mathbb R^d$; reason: the two forms agree by Eq. (M) (milestone `eq_M`)
-- source:
--   Diakonikolas, Diakonikolas, Wang, Zarifis, Learning Positive Linear Combinations of ReLUs in Fully Polynomial Time, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.2, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_SumReLU_reluSum
import Definitions.Def_SumReLU_filterMatrix
import Definitions.Def_SumReLU_events
import Definitions.Def_SumReLU_IsTopEigenvector

namespace SumReLU

/-- **Lemma 4.2** (the top eigenvector of a perturbed filtered matrix finds `w_{i*}`).

Diakonikolas, Diakonikolas, Wang, Zarifis, *Learning Positive Linear Combinations of ReLUs in
Fully Polynomial Time*, arXiv:2610.32940 (PDF sha256 66803576…6c48), Lemma 4.2, p.25 (PDF p.27): "Let ξ ∈ (0, 1/300] be a small absolute constant. Let w_i be unit
vectors in ℝᵈ, β_i ∈ [0, 1], i ∈ [k], and λ ∈ (0, √ξ/10] be less than a sufficiently small constant.
Let p = ⌈log(k/λ)/log(1 + ξ)⌉. Consider any i* ∈ [k] such that β_{i*} ≥ λ, and denote
A_{i*}(ξ) = {i ∈ [k] : |w_i · w_{i*}| ≤ 1 − ξ}. Draw and fix u from the distribution U. Let M_{2p+2}(u)
be the matrix defined in (M). Define the following "correlation" and "separation" events on U: (11).
Suppose u ∈ E^{Cor}_{i*} ∩ E^{Sep}_{i*}. Let M̂_{2p+2}(u) be any real symmetric matrix such that
‖M̂_{2p+2}(u) − M_{2p+2}(u)‖₂ ≤ (√ξ/3)‖M_{2p+2}(u)‖₂. Then, the top eigenvector r̂₁ of M̂_{2p+2}(u)
satisfies |r̂₁ · w_{i*}| ≥ 0.99."

**Formalization Note.**
* "less than a sufficiently small constant" is subsumed by `λ ≤ √ξ/10`: with `ξ ≤ 1/300` the
  perturbation argument closes for every such `λ`; no further unnamed constant is introduced.
* `u` is any vector of `ℂᵈ` and `Z = Z_p(U)` any positive real; `M_{2p+2}(u)` is form (ii) of
  (M) (`filterMatrix`; its equality with form (i) is `eq_M`).
* "the top eigenvector" is every unit eigenvector of the largest eigenvalue (`IsTopEigenvector`);
  `‖·‖₂` is the spectral norm. Natural logarithm in `p`. -/
theorem lemma_4_2 {d k : ℕ} (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1 / 300) (β : Fin k → ℝ)
    (w : Fin k → EuclideanSpace ℝ (Fin d)) (hf : InClass β w) (lam : ℝ) (hl0 : 0 < lam)
    (hl1 : lam ≤ Real.sqrt ξ / 10) (i₀ : Fin k) (hi₀ : lam ≤ β i₀) (Z : ℝ) (hZ : 0 < Z)
    (u : Fin d → ℂ) (hu : u ∈ corrEvent w i₀ (degree ξ k lam) Z ∩ sepEvent ξ w i₀)
    (Mhat : Matrix (Fin d) (Fin d) ℝ) (hsym : Mhat.IsSymm)
    (hclose : specNorm (Mhat - filterMatrix β w (degree ξ k lam) Z u) ≤
      Real.sqrt ξ / 3 * specNorm (filterMatrix β w (degree ξ k lam) Z u))
    (r : EuclideanSpace ℝ (Fin d)) (hr : IsTopEigenvector Mhat r) :
    (0.99 : ℝ) ≤ |inner ℝ r (w i₀)| := by sorry

end SumReLU
