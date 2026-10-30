-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_proposition22
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.proposition22
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:47:33.91243+00:00
-- url     : https://prove2.me/theorems/37e4e6f0-62e0-4f3a-9344-1cd8517447d1
-- title:
--   Proposition 22: nonzero Gram spectra and eigenvector transport
-- statement:
--   Let $N,d\ge2$. Write $\mathcal Y_j^{(d)}$ for the $j$-box Young diagrams of height at most $d$. Define $R=R_N^{(d)}$ by $R_{\alpha\mu}=1$ when $\mu$ is obtained from $\alpha$ by adding one box, and zero otherwise. Its column and row Gram matrices are $G=R^{\mathsf T}R$ and $H=RR^{\mathsf T}$, over $\mathbb R$.
--
--   The matrix $H$ is invertible, and its eigenvalues are precisely the nonzero eigenvalues of $G$, with the same multiplicities:
--
--   $$\operatorname{spec}(G)\setminus\{0\}=\operatorname{spec}(H),\qquad r(G)=r(H).$$
--
--   If $Gv=\lambda v$ with $v
--   e0$, $\lambda
--   e0$, then $Rv
--   e0$ and $H(Rv)=\lambda Rv$. Conversely, if $Hw=\lambda w$ with $w
--   e0$, then $R^{\mathsf T}w
--   e0$ and $G(R^{\mathsf T}w)=\lambda R^{\mathsf T}w$. Here $r$ denotes spectral radius. These maps transport the corresponding eigenspaces.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 14, Proposition 22: nonzero Gram spectra and eigenvector transport

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Proposition 22: H is invertible as a conclusion; the nonzero spectra, their
multiplicities, eigenvector transport and spectral radii agree (PDF p.14). -/
theorem proposition22 {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) :
    IsUnit (rowGram d N) ∧
    (spectrum ℝ (columnGram d N) \ {0}) = spectrum ℝ (rowGram d N) ∧
    (∀ r : ℝ, r ≠ 0 →
      (columnGram d N).charpoly.roots.count r = (rowGram d N).charpoly.roots.count r) ∧
    (∀ (r : ℝ) (v : Partition d N → ℝ), r ≠ 0 → v ≠ 0 →
      columnGram d N *ᵥ v = r • v →
      incidence d N *ᵥ v ≠ 0 ∧
        rowGram d N *ᵥ (incidence d N *ᵥ v) = r • (incidence d N *ᵥ v)) ∧
    (∀ (r : ℝ) (w : Partition d (N-1) → ℝ), w ≠ 0 →
      rowGram d N *ᵥ w = r • w →
      (incidence d N).transpose *ᵥ w ≠ 0 ∧
        columnGram d N *ᵥ ((incidence d N).transpose *ᵥ w) =
          r • ((incidence d N).transpose *ᵥ w)) ∧
    spectralRadius ℝ (columnGram d N) = spectralRadius ℝ (rowGram d N) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
