-- Prove2me | Theorems.Thm_SparseSDP_TwoSided_eq_280
-- name    : SparseSDP.TwoSided.eq_280
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:50.492926+00:00
-- url     : https://prove2.me/theorems/a7365ea2-0f33-4e80-9366-bd003a184dda
-- title:
--   Eq. (280), p. 53 — the mean-response regret bound of [CDST19, Theorem 2]
-- statement:
--   Let $R,r,\omega>0$ and $T\ge1$. For every sequence of real symmetric $n\times n$ gains $G_1,\dots,G_T$ with $\|G_t\|\le r\omega$, with $H_t=\sum_{\tau<t}G_\tau$ and the learning rate $\eta_X=(r\omega)^{-1}\sqrt{2\log(4n)/(3T)}$ of Algorithm 7,
--   $$
--   R\lambda_{\max}\Big(\sum_{t=1}^TG_t\Big)-\sum_{t=1}^T\langle G_t,R\bar P(\eta_X H_t)\rangle\le\frac{R\log(4n)}{\eta_X}+\frac{3R\eta_X}{2}\sum_{t=1}^T\|G_t\|^2\le\frac{R\log(4n)}{\eta_X}+\frac{3R\eta_Xr^2\omega^2T}{2}.
--   $$
--
--   The bound is deterministic, so adaptive gains cost nothing. It plays the role of the usual exponential-weights guarantee for the matrix player; note $\bar P(H)$ is not the Gibbs state.
--
--   Differences from the source:
--   - reading: the bound for the realized gains $G_t=rA_{J_t}$ of Algorithm 7 → every symmetric sequence with $\|G_t\|\le r\omega$, at $\eta=\eta_X$; reason: the page says it "applies deterministically to every realized gain sequence", and every such sequence is realized for some instance ($A_j:=G_j/r$, $m\ge T$)
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Eq. (280), p. 53

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_alg7

open Matrix
open scoped Matrix.Norms.L2Operator

namespace SparseSDP.TwoSided

/-- **Eq. (280)**, p. 53: the mean-response regret bound, [CDST19, Theorem 2].

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Eq. (280), p. 53.

As printed, deterministically for every symmetric gain sequence `G₁, …, G_T` with `‖G_t‖ ≤ rω`
(every such sequence is a realized gain sequence `G_t = rA_{J_t}` of Algorithm 7 for some
instance), with `H_t` the sum of the previous gains (`∑ τ ∈ range t` below sums the first `t`
gains, the paper's `H_{t+1}`), at the learning rate `η_X = (rω)⁻¹√(2log(4n)/(3T))` of Algorithm 7,
line 3. The first inequality is the regret bound; the second uses `‖G_t‖ ≤ rω`.

**Formalization Note.** The page states the bound at `η_X` only; no other learning rate is
claimed, so none is stated here. -/
theorem eq_280 {d : ℕ} [NeZero d] (G : ℕ → Mat d) (T : ℕ) (R r ω : ℝ)
    (hG : ∀ t < T, (G t).IsHermitian) (hGn : ∀ t < T, ‖G t‖ ≤ r * ω) (hT : 1 ≤ T) (hR : 0 < R)
    (hr : 0 < r) (hω : 0 < ω) :
    R * lamMax (∑ t ∈ Finset.range T, G t) -
        ∑ t ∈ Finset.range T,
          hs (G t) (R • Pbar (etaX d T r ω • ∑ τ ∈ Finset.range t, G τ)) ≤
      R * Real.log (4 * d) / etaX d T r ω +
        3 * R * etaX d T r ω / 2 * ∑ t ∈ Finset.range T, ‖G t‖ ^ 2 ∧
    R * Real.log (4 * d) / etaX d T r ω +
        3 * R * etaX d T r ω / 2 * ∑ t ∈ Finset.range T, ‖G t‖ ^ 2 ≤
      R * Real.log (4 * d) / etaX d T r ω + 3 * R * etaX d T r ω * r ^ 2 * ω ^ 2 * T / 2 := by sorry

end SparseSDP.TwoSided
