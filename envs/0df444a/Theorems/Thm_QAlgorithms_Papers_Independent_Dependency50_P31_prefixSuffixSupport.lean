-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P31_prefixSuffixSupport
-- name    : QAlgorithms.Papers.Independent.Dependency50.P31.prefixSuffixSupport
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:37:02.149827+00:00
-- url     : https://prove2.me/theorems/32529ef0-2a84-4100-9790-9a1ab0c9fd9c
-- title:
--   Prefix and suffix projectors and Schmidt support
-- statement:
--   Let $N\ge2$, $d\ge c_1$, and let $t$ be a standard tableau of shape $\nu$. Fix $1\le k\le N-1$, put $H_A=(\mathbb C^d)^{\otimes k}$ and $H_B=(\mathbb C^d)^{\otimes(N-k)}$, and let $t_A$ be the prefix tableau with labels $1,\ldots,k$. For every $\psi\in\operatorname{Im}P_t$ and every Schmidt decomposition $\psi=\sum_i\lambda_i\psi_i^A\otimes\psi_i^B$,
--
--   $$
--   (P_{t_A}\otimes I_{H_B})\psi=\psi,\qquad
--   \lambda_i>0\Longrightarrow\psi_i^A\in\operatorname{Im}P_{t_A}.
--   $$
--
--   Suppose that deleting the prefix, subtracting $k$ from the labels, and applying one common translation to the remaining boxes gives an ordinary standard tableau $t_B$. Then also
--
--   $$
--   (I_{H_A}\otimes P_{t_B})\psi=\psi,\qquad
--   \lambda_i>0\Longrightarrow\psi_i^B\in\operatorname{Im}P_{t_B},\qquad
--   \operatorname{Im}P_t\subseteq\operatorname{Im}P_{t_A}\otimes\operatorname{Im}P_{t_B}.
--   $$
--
--   These statements identify both physical supports without asserting equality of the tensor subspaces. They extend homogeneously to unnormalized vectors.
-- source:
--   Lower bound on entanglement in subspaces defined by Young diagrams, arXiv:1805.00364v2, PDF p. 12, Corollary 8, equations (34)–(36)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P31

open scoped ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

/-- Corollary 8, arXiv:1805.00364v2 PDF p.12, equations (34)-(36).
Both identities, both positive Schmidt-support conclusions, and the full subspace
inclusion are retained. The suffix condition uses one common translation. -/
theorem prefixSuffixSupport {d n : ℕ} (hn : 2 ≤ n) (nu : Schur.Partition d n)
    (t : Filling n) (ht : IsTableau nu.val t) (k : ℕ) (hk0 : 1 ≤ k) (hk1 : k ≤ n-1)
    (psi : H d n) (hpsi : psi ∈ tableauSpace d t) :
    act (liftLeft k (by omega) (tableauProjector d (tableauPrefix t k (by omega)))) psi = psi ∧
    (∀ s : PhysicalSchmidtDecomposition psi k (by omega), ∀ i, 0 < s.coeff i →
      s.left i ∈ tableauSpace d (tableauPrefix t k (by omega))) ∧
    (∀ b : Filling (n-k), IsSuffix t k (by omega) b →
      act (liftRight k (by omega) (tableauProjector d b)) psi = psi ∧
      (∀ s : PhysicalSchmidtDecomposition psi k (by omega), ∀ i, 0 < s.coeff i →
        s.right i ∈ tableauSpace d b) ∧
      tableauSpace d t ≤ tensorSubspace k (by omega)
        (tableauSpace d (tableauPrefix t k (by omega))) (tableauSpace d b)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P31

end
