-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P32_conditional_fannes_common_classical_basis
-- name    : QAlgorithms.Papers.Independent.Gap48.P32.conditional_fannes_common_classical_basis
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:40:55.50802+00:00
-- url     : https://prove2.me/theorems/140309ef-6265-4dc9-ac33-9224f79e2890
-- title:
--   Conditional Fannes bound in a common classical conditioning basis
-- statement:
--   All registers are finite and have positive dimension. Density matrices are positive semidefinite with trace one, all pure vectors have norm one, and entropy is in bits. Write $S$ for von Neumann entropy, $I(A;B)=S(A)+S(B)-S(AB)$, and $I(A;B|E)=S(AE)+S(BE)-S(E)-S(ABE)$. The squashed entanglement $E_{\mathrm{sq}}(\rho)$ is the infimum of $I(A;B|E)/2$ over every finite quantum extension of $\rho$, with no common dimension cap or attainment assumption. All marginals below are actual partial traces.
--
--   Let $p_k,q_k$ be probability distributions, $\rho_k^A,\sigma_k^A$ density matrices, and $(|k\rangle)_k$ one common arbitrary orthonormal basis of $B$. Set $\rho=\sum_kp_k\rho_k^A\otimes|k\rangle\langle k|$ and $\sigma=\sum_kq_k\sigma_k^A\otimes|k\rangle\langle k|$. For $\epsilon\ge0$ with $\|\rho-\sigma\|_1\le\epsilon$, $$|S(A|B)_\rho-S(A|B)_\sigma|\le\eta(2\epsilon)+3\epsilon\log_2d_A,$$ where $S(A|B)=S(AB)-S(B)$ and $\eta(x)=-x\log_2x$ for $0\le x\le1/4$, $1/2$ otherwise. This bound is independent of the dimension of $B$ and does not require $A$ to be classical.
-- source:
--   "Squashed Entanglement" - An Additive Entanglement Measure, arXiv:quant-ph/0308088v3, PDF p. 7, Appendix A, (A1)--(A2)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P32

namespace QAlgorithms.Papers.Independent.Gap48.P32

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

local notation "sq" => QAlgorithms.Papers.Independent.Dependency50.P19.squashed

local notation "cmi" => QAlgorithms.Papers.Independent.Dependency50.P19.conditionalMutual

local notation "mi" => QAlgorithms.Papers.Independent.Dependency50.P19.mutualInformation

local notation "ef" => QAlgorithms.Papers.Independent.Information100.P08.formation

-- Reuse exact accepted generic tensor pairing and partial traces.

open QAlgorithms.Papers.Independent.Next46.P42 (regroupProduct)

open QAlgorithms.Papers.Independent.Information100.P08 (firstPair secondPair)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

section Bipartite

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [instAne : Nonempty A] [instBne : Nonempty B]

include instAne instBne

/-- PDF p.7, Appendix A: the conditional Fannes inequality for two states
classical in the SAME arbitrary B basis, without classicality of A. -/
theorem conditional_fannes_common_classical_basis
    (p q : B → ℝ) (hp : ∀ k, 0 ≤ p k) (hq : ∀ k, 0 ≤ q k)
    (hpsum : ∑ k, p k = 1) (hqsum : ∑ k, q k = 1)
    (rho sigma : B → Matrix A A ℂ)
    (hrho : ∀ k, IsDensityMatrix (rho k)) (hsigma : ∀ k, IsDensityMatrix (sigma k))
    (U : Matrix.unitaryGroup B ℂ) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hclose : traceNorm (commonBasisCQ p rho (U : Matrix B B ℂ) -
      commonBasisCQ q sigma (U : Matrix B B ℂ)) ≤ epsilon) :
    |conditionalEntropy (commonBasisCQ p rho (U : Matrix B B ℂ)) -
      conditionalEntropy (commonBasisCQ q sigma (U : Matrix B B ℂ))| ≤
      fannesEta (2*epsilon) + 3*epsilon*Real.logb 2 (Fintype.card A) := by sorry

end Bipartite

end

end QAlgorithms.Papers.Independent.Gap48.P32
