-- Prove2me | Theorems.Thm_TDHamSim_QueryOptimal_eq_81
-- name    : TDHamSim.QueryOptimal.eq_81
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T14:17:28.531601+00:00
-- url     : https://prove2.me/theorems/c8f6eabf-24fc-4ebf-8502-cc4f9ce1d0b0
-- title:
--   §6.5, eq. (81) — amplification block identity
-- statement:
--   Let $V$ be unitary on an auxiliary register and a system, fix its zero auxiliary state, and suppose $[V]_0=\widetilde U/2$. Define $R_W=2\Pi_{W,0}-I$ and $U_{\rm sim}=-VR_WV^\dagger R_WV$. Then
--
--   $$[U_{\rm sim}]_0=3[V]_0-4[V]_0[V]_0^\dagger[V]_0=\frac32\widetilde U-\frac12\widetilde U\widetilde U^\dagger\widetilde U.$$
--
--   The complete cubic identity and its sign convention are retained. This form can be reused for any normalization-two unitary block encoding.
--
--   Differences from the source:
--   - encoding: qubit Hilbert spaces, tensor registers and time labels → binary-string bases, finite coordinate matrices and Fin indices with the spectral norm; reason: a change of coordinates representing every source instance, with explicit direct-sum and flag encodings
--   - generalization: the normalization-two block encoding constructed in (74)–(75) → every finite-dimensional unitary V with zero block Uapprox/2; reason: the algebraic cubic identity specializes exactly to the constructed circuit
-- source:
--   Boyang Chen, Minbo Gao, Zhengfeng Ji, Tongyang Li, Xinzhao Wang, Shuo Zhou, STOC 2027 submission #383 (October 2026), §6.5, eq. (81) — amplification block identity, p.31. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/383.pdf

import Definitions.Def_TDHamSim_QueryOptimal_Model

open scoped Matrix.Norms.L2Operator

namespace TDHamSim.QueryOptimal

/-- Eq. (81), p.31, generalized to every unitary normalization-two block encoding. -/
theorem eq_81 {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq κ] [DecidableEq ι]
    (z : κ) (V : Mat (κ × ι)) (hV : IsUnitary V) (U : Mat ι)
    (hblock : block z V = (1/2 : ℂ) • U) :
    block z (amplify z V) = (3 : ℂ) • block z V -
      (4 : ℂ) • (block z V * (block z V).conjTranspose * block z V) ∧
    block z (amplify z V) = (3/2 : ℂ) • U - (1/2 : ℂ) • (U * U.conjTranspose * U) := by sorry

end TDHamSim.QueryOptimal
