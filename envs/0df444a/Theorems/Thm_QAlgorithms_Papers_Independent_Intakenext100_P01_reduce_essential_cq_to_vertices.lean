-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P01_reduce_essential_cq_to_vertices
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P01.reduce_essential_cq_to_vertices
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:17:02.00849+00:00
-- url     : https://prove2.me/theorems/f1b52f4b-c85f-4d83-9d80-1b66ed79cf0f
-- title:
--   Reduce a norm-one representation to extreme outputs
-- statement:
--   Let $T:M_d(\mathbb C)\to M_n(\mathbb C)$, $d,n\ge1$, be represented by a POVM $(M_i)_{i=1}^k$ and density matrices $(\sigma_i)_{i=1}^k$, with $\|M_i\|_{\mathrm{op}}=1$, as $T(A)=\sum_i\operatorname{Tr}(M_iA)\sigma_i$. Choose a sublist $\sigma_{j_1},\ldots,\sigma_{j_r}$ that lists exactly the distinct extreme points of the physical image. Then there is a POVM $(N_\ell)_{\ell=1}^r$ with every $\|N_\ell\|_{\mathrm{op}}=1$ such that
--   $$T(A)=\sum_{\ell=1}^{r}\operatorname{Tr}(N_\ell A)\sigma_{j_\ell}\quad\text{for every operator }A.$$
--   Duplicates are allowed in the original output list.
--
--   The new representation keeps the channel and selected output states unchanged.
-- source:
--   Quantum channels with polytopic images and image additivity, arXiv:1408.2340v1, PDF p. 12, Lemma 7.1

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

/-- Lemma 7.1, PDF p.12: replace a given norm-one POVM by one indexed only by the
distinct extreme outputs in the selected sublist, keeping the same channel and those outputs. -/
theorem reduce_essential_cq_to_vertices {d n k r : ℕ} (hd : 0 < d) (hn : 0 < n)
    (T : Superop (Fin d) (Fin n)) (hT : IsChannel T)
    (M : Fin k → Mat d) (s : Fin k → Mat n)
    (hM : IsPOVM M) (hNorm : ∀ i, specNorm (M i) = 1)
    (hs : ∀ i, IsDensityMatrix (s i)) (hRep : HasHolevoRepresentation T M s)
    (select : Fin r ↪ Fin k) (hDistinct : Function.Injective (s ∘ select))
    (hExtreme : (channelImage T).extremePoints ℝ = Set.range (s ∘ select)) :
    ∃ N : Fin r → Mat d, IsPOVM N ∧ (∀ i, specNorm (N i) = 1) ∧
      HasHolevoRepresentation T N (s ∘ select) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P01

end
