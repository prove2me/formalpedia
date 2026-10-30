-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_optimal_povm_trace
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.optimal_povm_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:15:48.355067+00:00
-- url     : https://prove2.me/theorems/a402215c-09db-4fd4-91ee-16684f3b8e8d
-- title:
--   Fact 20: uniform full POVM trace before and after optimization
-- statement:
--   Let $N\ge1$ be the number of ports and $d\ge2$ their local dimension. Each initial port is the normalized Bell vector $d^{-1/2}\sum_{i=1}^d|ii\rangle$. On Alice's $N$ ports and input, let $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes P^+_{a0}$, $\rho=\sum_a\sigma_a$, $\Pi_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$ (inverse zero on the kernel), $\Delta=I-\sum_a\Pi_a$, and $\widetilde\Pi_a=\Pi_a+\Delta/N$. Write $V_a^\prime$ for the swap of port $a$ and input, transposed only on input in the computational basis. For $r$ ports, let $v^{(r)}$ be nonnegative Euclidean-normalized coefficients selected by maximizing the physical deterministic teleportation objective (6), and set $O_r=d^{r/2}\sum_{\lambda\vdash r}v^{(r)}_\lambda P_\lambda/\sqrt{d_\lambda m_\lambda}$ using the actual central character projectors. At $r=0$ this is the scalar identity. Operators on fewer registers are extended by identities. For every selected port $a$,
--   $$\operatorname{Tr}[(O_N^\dagger\otimes I)\widetilde\Pi_a(O_N\otimes I)]=\operatorname{Tr}\widetilde\Pi_a=\frac{d^{N+1}}{N}.$$
--   These are full traces on all Alice ports and input, and yield the actual optimized Born probabilities.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 22, Fact 20: uniform full POVM trace before and after optimization

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF p.22, Fact 20, (C2): full POVM trace, before and after the prescribed optimal operation. -/
theorem optimal_povm_trace (d n : ℕ) (hd : 2 ≤ d)
    (v : Schur.Partition d (n + 1) → ℝ) (hv : IsOptimalCoefficients d (n + 1) v)
    (a : Fin (n + 1)) :
    ((extendInput (resourceOperation d (n + 1) v))ᴴ * fullEffect d (n + 1) a *
      extendInput (resourceOperation d (n + 1) v)).trace = (fullEffect d (n + 1) a).trace ∧
    (fullEffect d (n + 1) a).trace = ((d : ℂ) ^ (n + 2) / (n + 1 : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
