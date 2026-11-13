-- Prove2me | Theorems.Thm_TalagrandThinning_lemma_3_1
-- name    : TalagrandThinning.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:42.552677+00:00
-- url     : https://prove2.me/theorems/1e221d07-914f-4afa-9bc3-ae2e8a67abd3
-- title:
--   Lemma 3.1 — pointwise square bound
-- statement:
--   Let $0<t,p<1$, let $\mathcal U$ be an increasing family of subsets of $[N]$ and $f=\mathbf 1_{\mathcal U}$. For every deterministic $j,x\subseteq[N]$,
--
--   $$f(j\cap x)\le\big(L_jf(x)\big)^2.\qquad(3.1)$$
--
--   This is the only place where monotonicity of $\mathcal U$ enters; the right side is a square of a possibly negative real number.
--
--   Differences from the source:
--   - encoding: subsets $A\subseteq[N]=\{1,\dots,N\}$, $\cap$, $\subseteq$ → indicator vectors $x:\mathrm{Fin}\,N\to\mathrm{Bool}$ on $\{0,\dots,N-1\}$, $\sqcap$, $\le$; reason: the paper identifies a set with its indicator vector (p.2); relabelling the ground set changes no instance
--   - encoding: expectations $\mathbb E_{\mu_s}$ and laws as random variables → finite weighted sums $\sum_x \mu_s(\{x\})\,f(x)$ and measures on the finite cube; reason: the cube is finite, so expectation is a finite sum; same values
--   - encoding: the standing range of §2 ($\phi_s$ is defined for $s\in(0,1)$; $t,p$ are a retention probability and a density) → explicit hypotheses $0<t<1$, $0<p<1$; reason: a nondegeneracy condition that only excludes the parameters for which $\phi_t,\phi_p,\beta$ are undefined
--   - encoding: $\mathcal U$ increasing and $f=\mathbf 1_{\mathcal U}$ → `IsUpperSet U` and `U.indicator (fun _ => 1)`; reason: Mathlib names for the same notions
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), Lemma 3.1, eq. (3.1), p.4

import Mathlib
import Definitions.Def_TalagrandThinning_liftL

set_option autoImplicit false

namespace TalagrandThinning

/-- Lemma 3.1 (Pointwise square bound)
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, Lemma 3.1, eq. (3.1), p.4).

Let `0 < t, p < 1`, let `U` be an increasing family and `f = 1_U`. For every deterministic
`j, x ⊆ [N]`, `f(j ∩ x) ≤ (L_j f(x))²`.

**Formalization Note** `U : Set (Cube N)` is increasing iff `IsUpperSet U` (`A ∈ U`, `A ⊆ B` ⟹
`B ∈ U`); `1_U` is `U.indicator (fun _ => 1)`. `L_j f(x)` is a real number, possibly negative. -/
theorem lemma_3_1 {N : ℕ} (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (U : Set (Cube N)) (hU : IsUpperSet U) (j x : Cube N) :
    U.indicator (fun _ => (1 : ℝ)) (j ⊓ x) ≤
      (liftL t p j (U.indicator (fun _ => (1 : ℝ))) x) ^ 2 := by sorry

end TalagrandThinning
