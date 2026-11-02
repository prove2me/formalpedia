-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P95_lemma23
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P95.lemma23
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:42:20.536552+00:00
-- url     : https://prove2.me/theorems/4b0c3117-790f-4d5e-affc-64c34e358809
-- title:
--   Lemma 23: exchange of fixed coordinates on cuboid faces
-- statement:
--   Let $\lambda=(\lambda_1,\ldots,\lambda_d)$ be a finite probability vector: every entry is nonnegative and the entries sum to one. Write $\rho_\lambda=\sum_{i,j}\sqrt{\lambda_i\lambda_j}|ii\rangle\langle jj|$. All logarithms have base two. A PPT operation is a completely positive, trace-preserving map $L$ such that $\Gamma_{\rm out}L\Gamma_{\rm in}$ is completely positive for arbitrary finite ancillary systems; $\Gamma$ transposes Bob in the fixed product basis. Assume in addition that all entries of $\lambda$ are strictly positive, so $d$ is its Schmidt rank. Let $K\ge2$, and define the quadratic function $\Delta(x)=\sum_{i>j}x_ix_j/(K-1)-\sum_{i\ge j}x_ix_j/(K+1)$. For a set $C$ of coordinate indices, let $F_C$ be the closed face $|x_i|\le\sqrt{\lambda_i}$ with $x_i=\sqrt{\lambda_i}$ for $i\in C$. A stationary point means a point on $F_C$ whose derivative vanishes in every free affine-hull direction. Let $C_1=C_0\cup\{n_1\}$ and $C_2=C_0\cup\{n_2\}$, where $n_1,n_2$ are distinct and outside $C_0$. If $F_{C_1}$ contains a stationary point and $\lambda_{n_1}>\lambda_{n_2}$, then $F_{C_2}$ also contains one and
--
--   $$\Delta_{C_2}\ge\Delta_{C_1},\qquad\Delta_C=\frac{K}{(K^2-1)(K+|C|-d)}\left[\left(\sum_{i\in C}\sqrt{\lambda_i}\right)^2-(K+|C|-d)\sum_{i\in C}\lambda_i\right].$$
--
--   This exchanges a fixed coordinate while improving the stationary value. The hypotheses force a nonzero denominator; negative denominators are allowed.
-- source:
--   Pure-state transformations and catalysis under operations that completely preserve positivity of partial transpose, arXiv:0801.4322v2, PDF p. 11, Lemma 23: exchange of fixed coordinates on cuboid faces

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P95

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P95

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact primitives from the pinned accepted library; no local aliases.

open QAlgorithms.Papers.Independent.Claimed50.P28 (maximallyEntangledDensity)

open QAlgorithms.Papers.Independent.Information100.P27 (IsProbability)

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Information100.P19 (outer)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)

/-- PDF pp.11–12, Lemma 23: exchanging one fixed coordinate on a closed cuboid
face. Stationarity is in the affine hull; denominator signs are not silently restricted.
Set unions in the printed statement mean unions with singletons. -/
theorem lemma23 {d : ℕ} (K : ℕ) (hK : 2 ≤ K) (lam : Fin d → ℝ)
    (hprob : IsProbability lam) (hpos : ∀ i, 0 < lam i)
    (C0 : Finset (Fin d)) (n1 n2 : Fin d) (hn1 : n1 ∉ C0) (hn2 : n2 ∉ C0)
    (hne : n1 ≠ n2) (hgreater : lam n1 > lam n2)
    (hstationary : FaceStationary K lam (C0 ∪ {n1})) :
    FaceStationary K lam (C0 ∪ {n2}) ∧
      faceValue K lam (C0 ∪ {n1}) ≤ faceValue K lam (C0 ∪ {n2}) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P95

end
