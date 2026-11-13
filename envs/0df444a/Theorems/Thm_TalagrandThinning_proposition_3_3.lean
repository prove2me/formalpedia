-- Prove2me | Theorems.Thm_TalagrandThinning_proposition_3_3
-- name    : TalagrandThinning.proposition_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:45:41.992219+00:00
-- url     : https://prove2.me/theorems/ae4376b9-d86e-4266-a47f-e2c79e80df3a
-- title:
--   Proposition 3.3 — a positive majorant on the parent cube
-- statement:
--   Let $0<t,p<1$, let $\mathcal U$ be increasing and $f=\mathbf 1_{\mathcal U}$, and define
--
--   $$c_I=\Big(\frac{t(1-p)}{p(1-t)}\Big)^{|I|}\hat f_p(I)^2\qquad(I\subseteq[N]).\qquad(3.4)$$
--
--   Then every $c_I$ is nonnegative, and for every deterministic parent $j$, with $X_t\sim\mu_t$,
--
--   $$\mathbb P(j\cap X_t\in\mathcal U)\le\sum_{I\subseteq j}c_I.\qquad(3.5)$$
--
--   The coefficients depend only on $\mathcal U,t,p$, not on any parent law; averaging (3.5) over $J\sim\nu$ then only needs the probabilities $\mathbb P(I\subseteq J)$, which spreadness controls.
--
--   Differences from the source:
--   - encoding: subsets $A\subseteq[N]=\{1,\dots,N\}$, $\cap$, $\subseteq$ → indicator vectors $x:\mathrm{Fin}\,N\to\mathrm{Bool}$ on $\{0,\dots,N-1\}$, $\sqcap$, $\le$; reason: the paper identifies a set with its indicator vector (p.2); relabelling the ground set changes no instance
--   - encoding: the standing range of §2 ($\phi_s$ is defined for $s\in(0,1)$; $t,p$ are a retention probability and a density) → explicit hypotheses $0<t<1$, $0<p<1$; reason: a nondegeneracy condition that only excludes the parameters for which $\phi_t,\phi_p,\beta$ are undefined
--   - encoding: $\mathcal U$ increasing and $f=\mathbf 1_{\mathcal U}$ → `IsUpperSet U` and `U.indicator (fun _ => 1)`; reason: Mathlib names for the same notions
--   - encoding: $\mathbb P(j\cap X_t\in\mathcal U)$ → $\mu_t(\{x: j\cap x\in\mathcal U\})$ in $[0,\infty]$, compared with `ENNReal.ofReal` of the real sum; reason: the probability is a finite measure value; same comparison
--   - encoding: "the coefficients … are independent of the parent law $\nu$" → $c_I$ written inline as a formula in $\mathcal U,t,p$ only; reason: structural: no parent law appears in the statement
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), Proposition 3.3, eqs. (3.4)–(3.5), p.4

import Mathlib
import Definitions.Def_TalagrandThinning_liftL

set_option autoImplicit false

open MeasureTheory

namespace TalagrandThinning

/-- Proposition 3.3 (A positive majorant on the parent cube)
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, Proposition 3.3, eqs. (3.4)–(3.5), p.4; proof p.5).

Let `0 < t, p < 1`, `U` increasing, `f = 1_U`, and
`c_I = (t(1 − p)/(p(1 − t)))^{|I|} f̂_p(I)²` (3.4). Then every `c_I` is nonnegative, and for every
deterministic parent `j`, `P(j ∩ X_t ∈ U) ≤ ∑_{I⊆j} c_I` (3.5), with `X_t ∼ µ_t`.

**Formalization Note** `P(j ∩ X_t ∈ U)` is `µ_t {x | j ⊓ x ∈ U}` (a value in `ℝ≥0∞`), compared with
`ENNReal.ofReal` of the real sum. The coefficients `c_I` are written out in the statement; they
depend only on `U, t, p` (no parent law appears), which is the proposition's last sentence. -/
theorem proposition_3_3 {N : ℕ} (t p : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hp0 : 0 < p) (hp1 : p < 1)
    (U : Set (Cube N)) (hU : IsUpperSet U) :
    (∀ I : Finset (Fin N), 0 ≤ (t * (1 - p) / (p * (1 - t))) ^ I.card *
        fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2) ∧
    (∀ j : Cube N, prodLaw N t {x : Cube N | j ⊓ x ∈ U} ≤
      ENNReal.ofReal (∑ I ∈ (Finset.univ.filter (fun i => j i = true)).powerset,
        (t * (1 - p) / (p * (1 - t))) ^ I.card *
          fourierCoeff p (U.indicator (fun _ => (1 : ℝ))) I ^ 2)) := by sorry

end TalagrandThinning
