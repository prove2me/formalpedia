-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_proposition_7
-- name    : TDHamSim.QueryOptimal.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:23:43.209571+00:00
-- url     : https://prove2.me/theorems/0c321281-0041-4acc-86d1-d3a1cbe4c4ca
-- title:
--   Proposition 7 — factorial decay
-- statement:
--   Under (7) and Definition 3, let $q$ be an integer satisfying $q\ge\max\{1,\alpha T\}$, and let $J=2^m\ge q$. For $Q(z)=(1+z^2)/2$ and the private transducer block $A$,
--
--   $$\|Q(A)^q\|\le\left(\frac{12e\alpha T}{q}\right)^q.$$
--
--   The constant and the integer-domain restrictions are those of the paper. The bound is uniform in the time resolution and does not require commuting oracle blocks.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), Proposition 7 — factorial decay, p.21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_LCU

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- Proposition 7, p.21, including the constant 12e. -/
theorem proposition_7 {n a : ℕ} (m q : ℕ) (H : ℝ → Mat (Bits n))
    (O : Fin (2^m) → Mat (Bits a × Bits n)) (α β T : ℝ)
    (hα : 0 < α) (hβ : 0 ≤ β) (hT : 0 < T) (hH : IsHamiltonian H α β T)
    (hO : IsHAMT H α T O) (hq : 1 ≤ q) (hαT : α*T ≤ q) (hJ : q ≤ 2^m) :
    opNorm (Q (privateBlock (stepWeight α T (2^m)) O) ^ q) ≤ (12*Real.exp 1*α*T/q)^q := by sorry

end TDHamSim.QueryOptimal
