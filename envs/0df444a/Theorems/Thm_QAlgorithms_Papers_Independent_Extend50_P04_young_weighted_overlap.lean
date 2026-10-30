-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P04_young_weighted_overlap
-- name    : QAlgorithms.Papers.Independent.Extend50.P04.young_weighted_overlap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T13:17:15.498828+00:00
-- url     : https://prove2.me/theorems/23203a9b-68b0-4331-a512-cd49fbd165e2
-- title:
--   Proposition 22: Young-projector weighted overlap
-- statement:
--   Let $N\ge1$ be the number of ports and $d\ge2$ their local dimension. Each initial port is the normalized Bell vector $d^{-1/2}\sum_{i=1}^d|ii\rangle$. On Alice's $N$ ports and input, let $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes P^+_{a0}$, $\rho=\sum_a\sigma_a$, $\Pi_a=\rho^{-1/2}\sigma_a\rho^{-1/2}$ (inverse zero on the kernel), $\Delta=I-\sum_a\Pi_a$, and $\widetilde\Pi_a=\Pi_a+\Delta/N$. Write $V_a^\prime$ for the swap of port $a$ and input, transposed only on input in the computational basis. For a Young diagram $\lambda$, write $d_\lambda$ for its symmetric-group irrep dimension and $m_\lambda$ for its Schur–Weyl multiplicity at dimension $d$. Every summed diagram is physical (height at most $d$). For $\alpha\vdash N-1$, put $S_\alpha=\sum_{\nu\supset\alpha,\,\nu\vdash N}\sqrt{m_\nu d_\nu}$ and let $d_\theta$ be the dimension of its unique height-$(d+1)$ successor when $h(\alpha)=d$, zero otherwise. Define
--   $$T_{N,d}=\sum_{h(\alpha)<d}\frac{S_\alpha^2}{N}+\sum_{h(\alpha)=d}\frac{\sqrt{d_\alpha}S_\alpha^2}{\sqrt{Nd_\alpha-d_\theta}\sqrt N}.$$
--   Let $\mu\vdash N$ and $\alpha\vdash N-1$ be physical shapes. Let $P_\mu$ be the central character projector on all Alice ports and $P_\alpha$ the corresponding projector on all spectator Alice ports, extended by identities. Then
--   $$\operatorname{Tr}(P_\mu P_\alpha V_N^\prime\sqrt{\widetilde\Pi_N})=\mathbf1_{\alpha\subset\mu}\frac{d_\alpha S_\alpha\sqrt{m_\mu d_\mu}}{\sqrt{Nd_\alpha-d_\theta}\sqrt{Nd_\alpha}}.$$
--   The indicator is exactly zero unless the shapes differ by one added box. These are concrete character projectors, not arbitrary idempotents.
-- source:
--   Square-root measurements and degradation of the resource state in port-based teleportation scheme, arXiv:2105.14886v4, PDF p. 24, Proposition 22: Young-projector weighted overlap

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P04

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P04

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable

/-- PDF p.24, Proposition 22, (D11): overlap weighted by actual central character projectors.
Both radicals are retained, and the result is exactly zero for nonbranching shapes. -/
theorem young_weighted_overlap (d n : ℕ) (hd : 2 ≤ d)
    (alpha : Schur.Partition d n) (mu : Schur.Partition d (n + 1)) :
    (extendInput (Schur.isotypicProjector mu) *
      extendUnused (Fin.last n) (Schur.isotypicProjector alpha) *
      transposedSwap d (n + 1) (Fin.last n) *
      positiveRoot (fullEffect d (n + 1) (Fin.last n))).trace =
    ((if pbtOneBoxSuccessor alpha mu then
      (irrepDimension alpha : ℝ) * successorSum alpha * Real.sqrt (Schur.schurDimension mu * irrepDimension mu) /
        (Real.sqrt ((n + 1 : ℝ) * irrepDimension alpha - forbiddenDimension alpha) *
          Real.sqrt ((n + 1 : ℝ) * irrepDimension alpha)) else 0) : ℂ) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P04

end
