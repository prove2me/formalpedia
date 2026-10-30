-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_optimal_trace
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.optimal_trace
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:16:41.220991+00:00
-- url     : https://prove2.me/theorems/dd7b09d4-ec6b-4c48-9953-5f3809cdf565
-- title:
--   Theorem 21: operational optimal one-round trace formula
-- statement:
--   Let $N\ge1$ be the number of ports and $d\ge2$ their local dimension. Each initial port is the normalized Bell vector $d^{-1/2}\sum_{i=1}^d|ii\rangle$. On Alice's $N$ ports and input, let $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes P^+_{a0}$, $\rho=\sum_a\sigma_a$, $\Pi_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$ (inverse zero on the kernel), $\Delta=I-\sum_a\Pi_a$, and $\widetilde\Pi_a=\Pi_a+\Delta/N$. Write $V_a^\prime$ for the swap of port $a$ and input, transposed only on input in the computational basis. Here $F_{\rm rec}$ is the Born-weighted average of the unsquared absolute overlaps of normalized whole output branches with the ideal state, retaining the teleported Bell pair and all unused ports. The measurement instrument is $\sqrt{\widetilde\Pi_a}$; $F_{\rm non}$ uses identity resource operations. For $r$ ports, let $v^{(r)}$ be nonnegative Euclidean-normalized coefficients selected by maximizing the physical deterministic teleportation objective (6), and set $O_r=d^{r/2}\sum_{\lambda\vdash r}v^{(r)}_\lambda P_\lambda/\sqrt{d_\lambda m_\lambda}$ using the actual central character projectors. At $r=0$ this is the scalar identity. Operators on fewer registers are extended by identities. Extend $O_{N-1}$ only onto unused Alice ports, and write this embedding as $\widehat O_{N-1}$. At the last port,
--   $$F_{\rm opt}(N,d)=\frac{\sqrt N}{d}\left|\operatorname{Tr}(\sigma_N\sqrt{\widetilde\Pi_N}(O_N\otimes I)\widehat O_{N-1}^\dagger)\right|.$$
--   This evaluates the operational fidelity using the prescribed optimal resources and actual branch probabilities.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 22, Theorem 21: operational optimal one-round trace formula

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF pp.22-24, Theorem 21, (D6): operational optimized one-round unsquared fidelity.
The unused-resource operation is embedded on spectator Alice registers only. -/
theorem optimal_trace (d n : ℕ) (hd : 2 ≤ d)
    (v : Schur.Partition d (n + 1) → ℝ) (w : Schur.Partition d n → ℝ)
    (hv : IsOptimalCoefficients d (n + 1) v) (hw : IsOptimalCoefficients d n w) :
    recyclingFidelity d n (resourceOperation d (n + 1) v) (resourceOperation d n w) =
      Real.sqrt (n + 1 : ℝ) / (d : ℝ) *
      ‖(pbtSignal d (n + 1) (Fin.last n) * positiveRoot (fullEffect d (n + 1) (Fin.last n)) *
        extendInput (resourceOperation d (n + 1) v) *
        (extendUnused (Fin.last n) (resourceOperation d n w))ᴴ).trace‖ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
