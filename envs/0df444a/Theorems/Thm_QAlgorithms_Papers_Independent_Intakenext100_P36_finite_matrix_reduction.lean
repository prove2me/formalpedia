-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P36_finite_matrix_reduction
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P36.finite_matrix_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T05:11:48.123543+00:00
-- url     : https://prove2.me/theorems/045c90ae-a77b-47de-8e89-f9afa888d2c4
-- title:
--   Exact finite matrix reduction of the CB norm
-- statement:
--   Let $n,k\ge1$, let $\phi:M_n\to M_k$ be complex-linear, and supply any finite representation $\phi(X)=\sum_{i=1}^m A_iXB_i$, where $A_i\in M_{k,n}$ and $B_i\in M_{n,k}$. Choose a basis $C_j$ of the span of the $B_i$ and coefficients $B_i=\sum_jd_{ij}C_j$. Put $D_j=\sum_id_{ij}A_i$, choose a basis $E_a$ of their span, write $D_j=\sum_ac_{ja}E_a$, and put $F_a=\sum_jc_{ja}C_j$. Such choices exist. For every such choice, both final indexed families are linearly independent and $\phi(X)=\sum_aE_aXF_a$.
--
--   For each invertible $S\in M_p$, define $H_i=\sum_jS_{ij}F_j$ and $G_j=\sum_i(S^{-1})_{ij}E_i$. These also represent $\phi$, and
--
--   $$\|\phi\|_{\rm cb}=\|\phi^\dagger\|_\diamond=\inf_{S\in GL_p(\mathbb C)}\sqrt{\left\|\sum_iG_iG_i^\dagger\right\|}\sqrt{\left\|\sum_iH_i^\dagger H_i\right\|}.$$
--
--   The same infimum results on restricting $S$ to positive definite matrices. Here $\phi^\dagger$ is the bilinear trace dual, characterized by $\operatorname{Tr}(\phi(X)Y)=\operatorname{Tr}(X\phi^\dagger(Y))$. All matrix norms are Euclidean operator norms, and the diamond norm uses the unnormalized trace norm. Empty reduced families give zero cost for the zero map.
--
--   This is the paper's finite preprocessing and exact minimization reduction; it states no finite-time minimization or sampling accuracy guarantee.
-- source:
--   Computing Stabilized Norms for Quantum Operations via the Theory of Completely Bounded Maps, arXiv:0711.3636v1, PDF p. 10, §4.1, unnumbered main result: exact finite matrix reduction for the CB/diamond norm

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P36

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakenext100.P36

local notation "Mat" => QAlgorithms.Papers.Independent.Information100.P50.M

local notation "Map" => QAlgorithms.Papers.Independent.Information100.P50.Lin

open QAlgorithms.Papers.Independent.Dependency50.P49 (traceDual)

/-- PDF p.10: exact finite preprocessing followed by the invertible/positive
infimum formula. This asserts no finite-time exact minimization or sampling accuracy.
The p.12 reference to only Steps 1–2 is read as both eliminations, Steps 1–3. -/
theorem finite_matrix_reduction {n k m : ℕ} (hn : 0 < n) (hk : 0 < k)
    (phi : Map n k) (A : Fin m → Matrix (Fin k) (Fin n) ℂ)
    (B : Fin m → Matrix (Fin n) (Fin k) ℂ) (hrep : IsGeneralizedChoiKraus phi A B) :
    Nonempty (BasisReduction A B) ∧
    ∀ r : BasisReduction A B,
      LinearIndependent ℂ (reducedRight r) ∧
      IsGeneralizedChoiKraus phi r.E (reducedRight r) ∧
      (∀ S : Mat r.p, IsUnit S →
        IsGeneralizedChoiKraus phi (changedLeft r.E S) (changedRight (reducedRight r) S)) ∧
      extendedCBNorm phi = rectangularDiamondNorm (traceDual phi) ∧
      extendedCBNorm phi = sInf {v : ℝ≥0∞ | ∃ S : Mat r.p, IsUnit S ∧
        v = ENNReal.ofReal (changeCost r.E (reducedRight r) S)} ∧
      extendedCBNorm phi = sInf {v : ℝ≥0∞ | ∃ S : Mat r.p, S.PosDef ∧
        v = ENNReal.ofReal (changeCost r.E (reducedRight r) S)} := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P36

end
