-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_signal_symmetries
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.signal_symmetries
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:08:55.288156+00:00
-- url     : https://prove2.me/theorems/989cd8ff-0a25-4572-9337-defd06adae08
-- title:
--   §II, Eqs.(10)–(14): signal symmetries, covariance and Bell partial transpose
-- statement:
--   Let $N\ge1$ be the number of ports and $d\ge2$ their local dimension. Each initial port is the normalized Bell vector $d^{-1/2}\sum_{i=1}^d|ii\rangle$. On Alice's $N$ ports and input, let $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes P^+_{a0}$, $\rho=\sum_a\sigma_a$, $\Pi_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$ (inverse zero on the kernel), $\Delta=I-\sum_a\Pi_a$, and $\widetilde\Pi_a=\Pi_a+\Delta/N$. Write $V_a^\prime$ for the swap of port $a$ and input, transposed only on input in the computational basis. Let $V(\pi)$ permute the Alice ports. For each port $a$, every unitary $U\in U(d)$, and every permutation $\pi\in S_N$,
--   $$[U^{\otimes N}\otimes\overline U,\sigma_a]=0,\qquad V(\pi)\sigma_aV(\pi)^\dagger=\sigma_{\pi(a)},\qquad V(\pi)\widetilde\Pi_aV(\pi)^\dagger=\widetilde\Pi_{\pi(a)}.$$
--   If $\pi(a)=a$, then $[V(\pi),\sigma_a]=0$. Moreover $\rho$ is permutation invariant, and
--   $$I_{\bar a}\otimes P^+_{a0}=V_a^\prime/d,\qquad\rho=d^{-N}\sum_a V_a^\prime.$$
--   These identities identify the protocol symmetries and the physical partially transposed operators.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 6, §II, Eqs.(10)–(14): signal symmetries, covariance and Bell partial transpose

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF p.6, (10)-(14): signal symmetries, completed-measurement covariance and Bell partial transpose.
The subgroup fixing a depends on a; the printed sigma(a) in (12) means pi(a). -/
theorem signal_symmetries (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N) :
    (∀ (a : Fin N) (U : Matrix.unitaryGroup (Fin d) ℂ),
      pbtCollectiveAction d N U * pbtSignal d N a = pbtSignal d N a * pbtCollectiveAction d N U) ∧
    (∀ (a : Fin N) (pi : Equiv.Perm (Fin N)), pi a = a →
      portPermutation d N pi * pbtSignal d N a = pbtSignal d N a * portPermutation d N pi) ∧
    (∀ (a : Fin N) (pi : Equiv.Perm (Fin N)),
      portPermutation d N pi * pbtSignal d N a * (portPermutation d N pi)ᴴ = pbtSignal d N (pi a)) ∧
    (∀ (a : Fin N) (pi : Equiv.Perm (Fin N)),
      portPermutation d N pi * fullEffect d N a * (portPermutation d N pi)ᴴ = fullEffect d N (pi a)) ∧
    (∀ pi : Equiv.Perm (Fin N),
      portPermutation d N pi * signalSum d N = signalSum d N * portPermutation d N pi) ∧
    (∀ a : Fin N, pbtBellProjector d N a = (d : ℂ)⁻¹ • transposedSwap d N a) ∧
    signalSum d N = ((d : ℂ) ^ N)⁻¹ • ∑ a, transposedSwap d N a := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
