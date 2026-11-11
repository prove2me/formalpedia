-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_eq_13
-- name    : TDHamSim.QueryOptimal.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:18:34.190404+00:00
-- url     : https://prove2.me/theorems/87fdce39-b14f-4c6e-85c0-464db1d5865c
-- title:
--   §4.1, eq. (13) — local Cayley error
-- statement:
--   Let $K$ be Hermitian on an $n$-qubit system, let $\alpha>0$ with $\|K\|\le\alpha$, and let $0<w\le1$. For the Cayley step defined above,
--
--   $$\|U^C-e^{-iwK/\alpha}\|\le w^3/12.$$
--
--   This is the local spectral-norm error bound used in the discretization estimate. The matrix $K$ represents the Hamiltonian at a sampled time; no commutativity between different samples is required.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), §4.1, eq. (13) — local Cayley error, p.13. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Cayley

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- §4.1, eq. (13), p.13: local spectral-norm error. -/
theorem eq_13 {n : ℕ} (K : Mat (Bits n)) (α w : ℝ) (hα : 0 < α)
    (hw : 0 < w) (hw1 : w ≤ 1) (hK : K.IsHermitian) (hbound : opNorm K ≤ α) :
    opNorm (cayley α w K - NormedSpace.exp ((-Complex.I * (w / α : ℝ)) • K)) ≤ w^3/12 := by sorry

end TDHamSim.QueryOptimal
