-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P26_typical_projectors_accept
-- name    : QAlgorithms.Papers.Independent.Support50.P26.typical_projectors_accept
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-23T21:07:22.181826+00:00
-- url     : https://prove2.me/theorems/206aeaf8-1df7-4d00-b330-1a13eaa27f0a
-- title:
--   Appendix B, Lemma 3: both typical projectors accept supported typical pairs
-- statement:
--   Fix a finite classical–quantum broadcast channel, finite auxiliaries $U_1,U_2$, a joint law $p$, and a deterministic map $f:U_1\times U_2\to X$. Let $\rho_{u,v}^{B_1}=\operatorname{Tr}_{B_2}\rho_{f(u,v)}$, let $\omega_u=\sum_v p(v|u)\rho_{u,v}^{B_1}$, and let $\bar\rho=\sum_{u,v}p(u,v)\rho_{u,v}^{B_1}$. At null conditioning symbols choose any normalized conditional state; these symbols never occur in supported words. Fix orthonormal eigenbases of $\bar\rho$ and every $\omega_u$.
--
--   For every $0<\epsilon<1$ and every positive projector tolerances $\delta_{\rm bar},\delta_{\rm cond}$, there exist $\eta>0$ and $N\ge1$ such that, for every $n\ge N$ and every pair of words $u^n,v^n$ with no zero-probability input pair and with
--   $$
--   \left|\frac{N(a,b|u^n,v^n)}{n}-p(a,b)\right|\le\eta\quad\text{for all }a,b,
--   $$
--   the actual product output $\rho_{u^n,v^n}^{B_1^n}=\bigotimes_{i=1}^n\rho_{u_i,v_i}^{B_1}$ satisfies both
--   $$
--   \operatorname{Tr}\!\left[\Pi_{\bar\rho,\delta_{\rm bar}}^n\rho_{u^n,v^n}^{B_1^n}\right]\ge1-\epsilon,\qquad
--   \operatorname{Tr}\!\left[\Pi_{\omega_{u^n},\delta_{\rm cond}}\rho_{u^n,v^n}^{B_1^n}\right]\ge1-\epsilon.
--   $$
--   The averaged projector is the sum of eigenword projectors satisfying supported absolute-frequency strong typicality. The conditional projector applies this test separately within each block of positions with the same $U_1$ symbol, using that block's conditional eigenvalue law. An absent block contributes the identity. Both $\eta$ and $N$ are chosen before the words.
--
--   This supplies the simultaneous acceptance estimates needed in the Marton error analysis. The tolerance scaling and supported convention are the corrected reading of the Appendix B proof, recorded for independent moderation.
-- source:
--   Classical codes for quantum broadcast channels, arXiv:1111.3645v4, PDF p. 16, Appendix B, Lemma 3: both receiver-1 typical projectors accept every strongly jointly typical input pair

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P26

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Support50.P26

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from pinned accepted modules, under the independent-paper override.
-- No coding theorem or other paper's channel model is reused.

open QAlgorithms.Papers.Independent.Information100.P22 (Op quantumMI)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Claimed50.P08 (cqBlocks)

open QAlgorithms.Papers.Independent.Dependency50.P47 (Law)

variable {X B1 B2 W U V A B : Type}

variable [Fintype X] [Fintype B1] [Fintype B2] [Fintype W] [Fintype U] [Fintype V]

variable [Fintype A] [Fintype B]

variable [DecidableEq X] [DecidableEq B1] [DecidableEq B2] [DecidableEq W]

variable [DecidableEq U] [DecidableEq V] [DecidableEq A] [DecidableEq B]

/-- Appendix B, Lemma 3, PDF pp.16–19, equations (139)–(140).
Printed: p.17 frequency sets omit support and the marginal sentence keeps the same tolerance;
p.19 (174) equates a product with its linear lower bound.
Changed: exclude impossible input/eigenword symbols, choose eta and N after both positive
projector tolerances and before all words, and read (174) as a lower bound.
Why: impossible inputs can give zero projector acceptance, marginalization sums frequency
errors (as (152)–(154) explicitly account for), and the product has positive cross terms.
Both original acceptance conclusions and the block projectors (170) are retained.
Independently audited in MODERATION-r1.md; items.json records printed/changed/why. -/
theorem typical_projectors_accept (C : BroadcastChannel X B1 B2) (D : MartonData U V X)
    (Sbar : FiniteSpectralResolution B1 (averageState1 C D))
    (Scond : ∀ u, FiniteSpectralResolution B1 (conditionalState1 C D u)) :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
    ∀ deltaBar : ℝ, 0 < deltaBar → ∀ deltaCond : ℝ, 0 < deltaCond →
    ∃ eta : ℝ, 0 < eta ∧ ∃ N : ℕ, 0 < N ∧ ∀ n ≥ N,
      ∀ (u : Fin n → U) (v : Fin n → V),
        StrongTypical D.law.prob eta (fun i => (u i, v i)) →
        1 - epsilon ≤ effectProb (averagedProjector Sbar n deltaBar) (receiver1Word C D u v) ∧
        1 - epsilon ≤ effectProb (conditionalTypicalProjector C D Scond u deltaCond)
          (receiver1Word C D u v) := by sorry

end QAlgorithms.Papers.Independent.Support50.P26

end
