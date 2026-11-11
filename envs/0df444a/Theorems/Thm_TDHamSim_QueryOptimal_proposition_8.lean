-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_proposition_8
-- name    : TDHamSim.QueryOptimal.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:23:26.132413+00:00
-- url     : https://prove2.me/theorems/fdd54886-a088-4bff-b65c-b8a089b9a443
-- title:
--   Proposition 8 — combination of reuse lengths
-- statement:
--   Let the standing model hold, let $q\ge\max\{1,\alpha T\}$ be an integer, let $J=2^m\ge q$, and choose $b$ with $4q<2^b$. The coefficients of (52)–(55) satisfy
--
--   $$\sum_{N=1}^{4q}\lambda_N=1,\qquad\Lambda=2-2^{1-q}<2,$$
--   $$\|U_C-\widetilde U\|\le\sqrt{\alpha T}\left(\frac{12e\alpha T}{q}\right)^q.$$
--
--   All three conclusions concern the explicitly computed signed coefficients and reuse operators, rather than an arbitrary approximation with an assumed error certificate.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - encoding: an unspecified unitary completion of a uniform state preparation F_N → the explicit real Householder completion of that uniform column; reason: P_N depends only on the uniform column; this fixes a source choice without changing the encoded operator
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Proposition 8 — combination of reuse lengths, p.23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_LCU

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- Proposition 8, p.23: signed coefficients, exact normalization and full approximation error. -/
theorem proposition_8 {n a : ℕ} (m q b : ℕ) (H : ℝ → Mat (Bits n))
    (O : Fin (2^m) → Mat (Bits a × Bits n)) (α β T : ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hT : 0 < T) (hH : IsHamiltonian H α β T)
    (hO : IsHAMT H α T O) (hq : 1 ≤ q) (hαT : α*T ≤ q) (hJ : q ≤ 2^m) (hb : 4*q < 2^b) :
    (∑ r ∈ Finset.range (4*q), lambda q (r+1)) = 1 ∧
      normalization q = 2 - (2 : ℝ)^(1-(q : ℤ)) ∧ normalization q < 2 ∧
      opNorm (cayleyProduct H α T (2^m) - uTilde q b (stepWeight α T (2^m)) O) ≤
        Real.sqrt (α*T) * (12*Real.exp 1*α*T/q)^q := by sorry

end TDHamSim.QueryOptimal
