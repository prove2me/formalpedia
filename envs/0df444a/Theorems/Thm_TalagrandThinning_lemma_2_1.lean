-- Prove2me | Theorems.Thm_TalagrandThinning_lemma_2_1
-- name    : TalagrandThinning.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:29.946435+00:00
-- url     : https://prove2.me/theorems/da807228-0100-408a-8ac5-8a46ac00d871
-- title:
--   Lemma 2.1 — the one-coordinate kernel
-- statement:
--   Let $0<t,p<1$, $\beta=\sqrt{t(1-p)/(p(1-t))}$ and $h(x,w)=1+\beta\phi_t(x)\phi_p(w)$ for $x,w\in\{0,1\}$. Then
--
--   $$h(x,w)=1+\frac{(x-t)(w-p)}{p(1-t)}\qquad(2.3)$$
--
--   and the matrix of $h$ (rows $x=0,1$, columns $w=0,1$) is
--
--   $$\begin{pmatrix}h(0,0)&h(0,1)\\h(1,0)&h(1,1)\end{pmatrix}=\begin{pmatrix}\frac1{1-t}&\frac{p-t}{p(1-t)}\\0&\frac1p\end{pmatrix}.\qquad(2.4)$$
--
--   In particular $h(1,0)=0$ and $\mathbb E_{W\sim\mathrm{Bernoulli}(p)}h(x,W)=1$ for $x=0,1$ (2.5).
--
--   The zero entry $h(1,0)=0$ is what makes the product kernel vanish on non-contained configurations; the normalization makes $L_j1=1$.
--
--   **Formalization Note** $\mathbb E_{W\sim\mathrm{Bernoulli}(p)}g(W)$ is $(1-p)g(0)+p\,g(1)$.
--
--   Differences from the source:
--   - encoding: the standing range of §2 ($\phi_s$ is defined for $s\in(0,1)$; $t,p$ are a retention probability and a density) → explicit hypotheses $0<t<1$, $0<p<1$; reason: a nondegeneracy condition that only excludes the parameters for which $\phi_t,\phi_p,\beta$ are undefined
--   - encoding: $\mathbb E_{W\sim\mathrm{Bernoulli}(p)}h(x,W)$ → $(1-p)h(x,0)+p\,h(x,1)$; reason: expectation of a Bernoulli variable
--   - encoding: the matrix (2.4) → four equalities, one per entry; reason: same content
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), Lemma 2.1, eqs. (2.3)–(2.5), p.3

import Mathlib
import Definitions.Def_TalagrandThinning_liftL

set_option autoImplicit false

namespace TalagrandThinning

/-- Lemma 2.1 (The one-coordinate kernel)
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, Lemma 2.1, eqs. (2.3)–(2.5), p.3).

For `0 < t, p < 1`, the kernel `h(x, w) = 1 + β ϕ_t(x) ϕ_p(w)` satisfies
(2.3) `h(x, w) = 1 + (x − t)(w − p)/(p(1 − t))`;
(2.4) `h(0,0) = 1/(1 − t)`, `h(0,1) = (p − t)/(p(1 − t))`, `h(1,0) = 0`, `h(1,1) = 1/p`;
(2.5) `h(1,0) = 0` and `E_{W∼Bernoulli(p)} h(x, W) = 1` for `x = 0, 1`.

**Formalization Note** `x, w ∈ {0,1}` are `Bool`s read as `0`/`1`. `E_{W∼Bernoulli(p)} g(W)` is
`(1 − p) g(0) + p g(1)`. The standing range `0 < t, p < 1` is that of §2 (ϕ_t, ϕ_p, β need it). -/
theorem lemma_2_1 (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ x w : Bool, kernelH t p x w =
      1 + ((if x then 1 else 0) - t) * ((if w then 1 else 0) - p) / (p * (1 - t))) ∧
    kernelH t p false false = 1 / (1 - t) ∧
    kernelH t p false true = (p - t) / (p * (1 - t)) ∧
    kernelH t p true false = 0 ∧
    kernelH t p true true = 1 / p ∧
    (∀ x : Bool, (1 - p) * kernelH t p x false + p * kernelH t p x true = 1) := by sorry

end TalagrandThinning
