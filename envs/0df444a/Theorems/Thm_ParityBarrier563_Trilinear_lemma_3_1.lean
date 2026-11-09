-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_lemma_3_1
-- name    : ParityBarrier563.Trilinear.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:18.360753+00:00
-- url     : https://prove2.me/theorems/fd0554a4-98ee-43bc-9710-99d638a5e226
-- title:
--   Lemma 3.1 — if θ ≤ 1, a p-random restriction of a k-CNF has E size_b(H_ρ) ≤ 1
-- statement:
--   Let $k\ge0$ and $b\ge1$ be integers, let $H$ be a $k$-CNF on $\{0,1\}^V$, and let $0<p<1$ satisfy
--
--   $$\theta=\sum_{\ell=b+1}^{k}\binom{k}{\ell}\Bigl(\frac{2p}{1-p}\Bigr)^{\ell}\le1$$
--
--   (an empty sum, $\theta=0$, when $k<b+1$). Then for a $p$-random restriction $\rho$ of $V$,
--
--   $$\mathbb E_\rho\,\mathrm{size}_b(H_\rho)\le1 .$$
--
--   This restriction lemma lets bounds against narrow ($b$-CNF) tests control correlations with wide $k$-CNFs, whatever their number of clauses.
--
--   Differences from the source:
--   - encoding: E_ρ size_b(H_ρ) → the finite weighted sum over restrictions of size_b of the indicator of the restricted function, size_b being the infimum over representations; reason: for b ≥ 1 representations exist and the infimum is the source's minimum
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Lemma 3.1, printed p.12 (PDF p.14)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Correlation
import Definitions.Def_ParityBarrier563_Trilinear_Restriction

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-- Lemma 3.1, printed p.12 / PDF 14. -/
theorem lemma_3_1 (V : Type) [Fintype V] [DecidableEq V] (k b : ℕ) (p : ℝ) (H : BoolFn V)
    (hb : 1 ≤ b) (hH : IsCNF k H) (hp0 : 0 < p) (hp1 : p < 1)
    (hθ : ∑ ℓ ∈ Finset.Icc (b + 1) k, (k.choose ℓ : ℝ) * (2 * p / (1 - p)) ^ ℓ ≤ 1) :
    restrExpect p (fun ρ => sizeB b (ind (restrict ρ H))) ≤ 1 := by sorry

end ParityBarrier563.Trilinear
