-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P13_halfNoisyBalancedEnsemble
-- name    : QAlgorithms.Papers.Independent.Support50.P13.halfNoisyBalancedEnsemble
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:23:31.783229+00:00
-- url     : https://prove2.me/theorems/45eaedc4-0bc2-4923-8825-5c18571780e8
-- title:
--   A single balanced ensemble bounds every real output p-norm
-- statement:
--   Let $\Phi$ be a unital completely positive trace-preserving qubit channel, let $K\ge1$, and let $\rho$ be any positive semidefinite trace-one matrix on $\mathbb C^K\otimes\mathbb C^2$. Put $r=\operatorname{Tr}_1\rho$, tracing out the first register, and let $\sigma_3=\operatorname{diag}(1,-1)$. There exist an integer $N\ge1$, strictly positive real numbers $c_1,\ldots,c_N$ summing to one, and unitary qubit matrices $U_1,\ldots,U_N$, such that $\operatorname{Tr}(\sigma_3U_irU_i^*)=0$ for every $i$, and simultaneously for every finite real $p\ge1$,
--
--   $$
--   \|(I\otimes\Phi)(\rho)\|_p\le
--   m_p(0)^{-1}\nu_p(\Phi)\sum_{i=1}^N c_i
--   \bigl\|(I\otimes\Psi_0)\bigl((I\otimes U_i)\rho(I\otimes U_i^*)\bigr)\bigr\|_p.
--   $$
--
--   Here $\|A\|_p=(\operatorname{Tr}A^p)^{1/p}$ for positive matrices, $\nu_p(\Phi)$ is the supremum of this output norm over all qubit density matrices, $\Psi_0$ erases off-diagonal qubit entries, and $m_p(0)=2^{-1+1/p}>0$. The same ensemble may depend on $\Phi$ and $\rho$ but works for all $p$, which permits simultaneous use of the bound across the norm family.
-- source:
--   Additivity for a class of unital qubit channels, arXiv:quant-ph/0103156v2, PDF p. 6, Theorem 3, equations (19)–(20)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Support50.P13

open QAlgorithms.Papers.Independent.Gap48.P03
  (productChannel maximumOutputPNorm holevoQuantity depolarizingNormFactor
    phaseChannel qubitPauli)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Dependency50.P23 (ordinaryClassicalCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- King quant-ph/0103156v2, PDF p.6, Theorem 3, (19)-(20).
A single finite strictly positive ensemble works simultaneously for all real p>=1.
The reduced state is computed by tracing out the first register.
The superfluous closing parenthesis on the printed left side has no meaning. -/
theorem halfNoisyBalancedEnsemble
    (Phi : Superop (Fin 2) (Fin 2)) (hPhi : IsChannel Phi)
    (hPhiUnital : Phi 1 = 1)
    (K : ℕ) (hK : 0 < K)
    (rho : Matrix (Fin K × Fin 2) (Fin K × Fin 2) ℂ)
    (hrho : IsDensityMatrix rho) :
    ∃ (N : ℕ) (c : Fin N → ℝ) (U : Fin N → Matrix.unitaryGroup (Fin 2) ℂ),
      1 ≤ N ∧ (∀ i, 0 < c i) ∧ (∑ i, c i) = 1 ∧
      (∀ i, ((qubitPauli pauliZ) *
        conjSuperop (U i : Matrix (Fin 2) (Fin 2) ℂ) (traceLeft rho)).trace = 0) ∧
      ∀ p : ℝ, 1 ≤ p →
        schatten p (idTensorSuperop Phi rho) ≤
          (depolarizingNormFactor 2 0 p)⁻¹ * maximumOutputPNorm Phi p *
            ∑ i, c i * schatten p
              (idTensorSuperop (phaseChannel (1 : Matrix (Fin 2) (Fin 2) ℂ) 0)
                (idTensorSuperop (conjSuperop (U i : Matrix (Fin 2) (Fin 2) ℂ)) rho)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P13

end
