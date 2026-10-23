-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P43_entropyTypical
-- name    : QAlgorithms.Papers.Independent.Renew46.P43.entropyTypical
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:24:08.284845+00:00
-- url     : https://prove2.me/theorems/06db897e-0fb6-43f5-b32b-666394b7c2cc
-- title:
--   Lemma I.11: There is 0≤K_H(d)≤max{(log2 3)²,(log2 d)²}, uniformly for all state lists and delta>0: Tr(rho^n PiH)≥1−K_H/delta².
-- statement:
--   Let a nonzero finite system have dimension $d$, and choose a fine orthogonal spectral resolution, including zero eigenspaces and a basis inside degeneracies. All states are normalized, $n>0$, and all typicality tolerances are positive. Write $H$ for entropy in bits, $K_V=2\log_2(e)/e$, $K_H(d)=\max\{(\log_2 3)^2,(\log_2 d)^2\}$, and $h=\sum_iH(\rho_i)$. A shadow $B$ is an effect with state mass at least $\eta$. In the variance bounds put $c=K_Vd\alpha\sqrt n$, $t=2N(\rho)e^{-2\mu(\rho)^2\alpha^2}$, where $N$ counts the positive eigenvalues of $\sqrt{\rho(1-\rho)}$ and $\mu$ is their minimum, or zero on empty support. In the constant-typical bound $\eta(u)=-u\log_2u$, including $u=0$. The weak-law factor states may be noncommuting, with target $\widetilde\rho$ and operator-norm tolerance $\epsilon>0$.
--
--   $$
--   \exists K_H(d)\le\max\{(\log_2 3)^2,(\log_2 d)^2\}:\quad\operatorname{Tr}(\rho_1\otimes\cdots\otimes\rho_n\Pi_H)\ge1-K_H(d)/\delta^2.
--   $$
--
--   This is the source result with its stated operational or information-theoretic domain.
-- source:
--   Coding Theorems of Quantum Information Theory, arXiv:quant-ph/9907077v1, PDF p. 13, Lemma I.11

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P43

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P43

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Information100.P06 (Below)

open QAlgorithms.Papers.Independent.Information100.P60 (copies relativeBits)

open QAlgorithms.Papers.Independent.Dependency50.P19 (count both)

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma I.11, PDF pp.13-14: K_H depends only on dimension and precedes the
block length, all factor states and the positive tolerance. -/
theorem entropyTypical (d : ℕ) (hd : 0 < d) :
    ∃ K : ℝ, 0 ≤ K ∧ K ≤ entropyConstant d ∧ K = entropyConstant d ∧
    ∀ (n : ℕ), 0 < n → ∀ (S : Fin n → FineResolution d) (delta : ℝ), 0 < delta →
      effectProb (wordTensor (fun i => (S i).state)) (entropyProjector S delta) ≥ 1 - K / delta^2 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P43

end
