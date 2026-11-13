-- Prove2me | Theorems.Thm_TalagrandThinning_lemma_3_2
-- name    : TalagrandThinning.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:31.794663+00:00
-- url     : https://prove2.me/theorems/7c4e2ab0-5e41-4d27-8129-c79837f18e58
-- title:
--   Lemma 3.2 — Walsh expansion of the lifted function
-- statement:
--   Let $0<t,p<1$. For any real function $f$ on the cube, every deterministic $j\subseteq[N]$ and every $x$,
--
--   $$L_jf(x)=\sum_{I\subseteq j}\beta^{|I|}\hat f_p(I)\,\omega^{(t)}_I(x),\qquad(3.2)$$
--
--   and consequently
--
--   $$\mathbb E_{X_t\sim\mu_t}\big(L_jf(X_t)\big)^2=\sum_{I\subseteq j}\beta^{2|I|}\hat f_p(I)^2.\qquad(3.3)$$
--
--   The lift $L_j$ carries the $p$-biased expansion of $f$ to a $t$-biased one, damping level $|I|$ by $\beta^{|I|}$.
--
--   Differences from the source:
--   - encoding: subsets $A\subseteq[N]=\{1,\dots,N\}$, $\cap$, $\subseteq$ → indicator vectors $x:\mathrm{Fin}\,N\to\mathrm{Bool}$ on $\{0,\dots,N-1\}$, $\sqcap$, $\le$; reason: the paper identifies a set with its indicator vector (p.2); relabelling the ground set changes no instance
--   - encoding: expectations $\mathbb E_{\mu_s}$ and laws as random variables → finite weighted sums $\sum_x \mu_s(\{x\})\,f(x)$ and measures on the finite cube; reason: the cube is finite, so expectation is a finite sum; same values
--   - encoding: the standing range of §2 ($\phi_s$ is defined for $s\in(0,1)$; $t,p$ are a retention probability and a density) → explicit hypotheses $0<t<1$, $0<p<1$; reason: a nondegeneracy condition that only excludes the parameters for which $\phi_t,\phi_p,\beta$ are undefined
--   - encoding: sums over $I\subseteq j$ → sums over the powerset of $\{i: j_i=1\}$; reason: same index set
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), Lemma 3.2, eqs. (3.2)–(3.3), p.4

import Mathlib
import Definitions.Def_TalagrandThinning_liftL

set_option autoImplicit false

namespace TalagrandThinning

/-- Lemma 3.2 (Walsh expansion of the lifted function)
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, Lemma 3.2, eqs. (3.2)–(3.3), p.4).

Let `0 < t, p < 1`. For any real function `f` on the cube and every deterministic `j`,
(3.2) `L_j f(x) = ∑_{I⊆j} β^{|I|} f̂_p(I) ω^{(t)}_I(x)`, and consequently
(3.3) `E_{X_t∼µ_t} (L_j f(X_t))² = ∑_{I⊆j} β^{2|I|} f̂_p(I)²`.

**Formalization Note** "`I ⊆ j`" ranges over the subsets of `{i | j i = true}`. -/
theorem lemma_3_2 {N : ℕ} (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (f : Cube N → ℝ) (j : Cube N) :
    (∀ x : Cube N, liftL t p j f x =
      ∑ I ∈ (Finset.univ.filter (fun i => j i = true)).powerset,
        beta t p ^ I.card * fourierCoeff p f I * omega t I x) ∧
    expect t (fun x => liftL t p j f x ^ 2) =
      ∑ I ∈ (Finset.univ.filter (fun i => j i = true)).powerset,
        beta t p ^ (2 * I.card) * fourierCoeff p f I ^ 2 := by sorry

end TalagrandThinning
