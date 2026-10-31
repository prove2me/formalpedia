-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_essential_cq_povm_geometry
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.essential_cq_povm_geometry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:21:39.918933+00:00
-- url     : https://prove2.me/theorems/208113a6-0234-4397-9f34-a31ace5863c2
-- title:
--   Norm-one POVM geometry and the exact image
-- statement:
--   Let $d,n\ge1$ and let $T(A)=\sum_{i=1}^k\operatorname{Tr}(M_iA)\sigma_i$ be a quantum channel, where $(M_i)$ is a POVM, every $\|M_i\|_{\mathrm{op}}=1$, and each $\sigma_i$ is a density matrix. There exist an orthonormal family $(e_i)_{i=1}^k$ and positive semidefinite matrices $R_i$, supported on $V^\perp$ for $V=\operatorname{span}\{e_i\}$, with
--   $$M_i=e_ie_i^*+R_i,\qquad\sum_iR_i=P_{V^\perp},\qquad\operatorname{Tr}(R_ie_je_j^*)=0\quad\text{for all }i,j.$$
--   Here $\dim_{\mathbb C}V=k$, and the residual matrices form a POVM on $V^\perp$, even when that space is zero. Moreover,
--   $$\operatorname{Im}T=\operatorname{conv}\{\sigma_1,\ldots,\sigma_k\}.$$
--
--   This explains the polytopic geometry of norm-one measure-and-prepare representations.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 3, §2, unnumbered: norm-one POVM decomposition and polytopic image

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P01

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakenext100.P01

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Information100.P07 (projection)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)

open QAlgorithms.Papers.Independent.Dependency50.P05 (renyiEntropy)

/-- §2, equations (2)–(3), PDF p.3: norm-one POVMs conclude an orthonormal family,
a residual POVM on its orthogonal complement, annihilation, and the exact output hull. -/
theorem essential_cq_povm_geometry {d n k : ℕ} (hd : 0 < d) (hn : 0 < n)
    (T : Superop (Fin d) (Fin n)) (hT : IsChannel T)
    (M : Fin k → Mat d) (s : Fin k → Mat n)
    (hM : IsPOVM M) (hNorm : ∀ i, specNorm (M i) = 1)
    (hs : ∀ i, IsDensityMatrix (s i)) (hRep : HasHolevoRepresentation T M s) :
    (∃ e : Fin k → EuclideanSpace ℂ (Fin d), ∃ R : Fin k → Mat d,
      Orthonormal ℂ e ∧
      (let V := Submodule.span ℂ (Set.range e)
       Module.finrank ℂ V = k ∧
       (∀ i, M i = pureDensity (e i) + R i) ∧
       (∀ i, (R i).PosSemidef ∧ IsSupportedOn (Vᗮ) (R i)) ∧
       (∑ i, R i) = projection (Vᗮ) ∧
       (∀ i j, (R i * pureDensity (e j)).trace = 0))) ∧
    channelImage T = convexHull ℝ (Set.range s) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
