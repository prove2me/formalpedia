-- Prove2me | Theorems.Thm_TalagrandThinning_lemma_2_2
-- name    : TalagrandThinning.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:50.876107+00:00
-- url     : https://prove2.me/theorems/5a07656a-4a50-4d55-b316-b27d0d06be79
-- title:
--   Lemma 2.2 — normalization and noncontainment
-- statement:
--   Let $0<t,p<1$. For every $j,x,w\subseteq[N]$,
--
--   $$j\cap x\not\subseteq w\implies k_j(x,w)=0.\qquad(2.7)$$
--
--   Moreover $L_j\mathbf 1=1$ (as a function of $x$) for every $j$.
--
--   The product kernel thus vanishes unless the thinned parent $j\cap x$ is contained in the target $w$, while integrating to one against $\mu_p$.
--
--   Differences from the source:
--   - encoding: subsets $A\subseteq[N]=\{1,\dots,N\}$, $\cap$, $\subseteq$ → indicator vectors $x:\mathrm{Fin}\,N\to\mathrm{Bool}$ on $\{0,\dots,N-1\}$, $\sqcap$, $\le$; reason: the paper identifies a set with its indicator vector (p.2); relabelling the ground set changes no instance
--   - encoding: expectations $\mathbb E_{\mu_s}$ and laws as random variables → finite weighted sums $\sum_x \mu_s(\{x\})\,f(x)$ and measures on the finite cube; reason: the cube is finite, so expectation is a finite sum; same values
--   - encoding: the standing range of §2 ($\phi_s$ is defined for $s\in(0,1)$; $t,p$ are a retention probability and a density) → explicit hypotheses $0<t<1$, $0<p<1$; reason: a nondegeneracy condition that only excludes the parameters for which $\phi_t,\phi_p,\beta$ are undefined
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), Lemma 2.2, eq. (2.7), p.3

import Mathlib
import Definitions.Def_TalagrandThinning_liftL

set_option autoImplicit false

namespace TalagrandThinning

/-- Lemma 2.2 (Normalization and noncontainment)
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, Lemma 2.2, eq. (2.7), p.3; proof p.4).

For `0 < t, p < 1` and every `j, x, w ⊆ [N]`: if `j ∩ x ⊈ w` then `k_j(x, w) = 0` (2.7);
moreover `L_j 1 = 1` for every `j`.

**Formalization Note** `j ∩ x ⊈ w` is `¬ (j ⊓ x ≤ w)`; `L_j 1 = 1` is stated pointwise in `x`. -/
theorem lemma_2_2 {N : ℕ} (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ j x w : Cube N, ¬ (j ⊓ x ≤ w) → kernelK t p j x w = 0) ∧
    (∀ j x : Cube N, liftL t p j (fun _ => 1) x = 1) := by sorry

end TalagrandThinning
