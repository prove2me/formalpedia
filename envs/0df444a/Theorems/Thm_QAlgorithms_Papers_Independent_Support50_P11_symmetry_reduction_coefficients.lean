-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_symmetry_reduction_coefficients
-- name    : QAlgorithms.Papers.Independent.Support50.P11.symmetry_reduction_coefficients
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:16:48.62753+00:00
-- url     : https://prove2.me/theorems/239864fb-90f5-4f5b-af91-7da65f8d566a
-- title:
--   Appendix A (A1)–(A3): symmetry reduction coefficients
-- statement:
--   Let $d\ge2$, $n,K\ge1$, and $0\le\alpha\le1$. On the $n$ input–output pairs let $E_j$ sum all products with exactly $j$ antisymmetric projectors and $n-j$ symmetric projectors. Let $\Upsilon_i$ sum products with exactly $i$ normalized Bell projectors and $n-i$ complements. The $E_j$ are orthogonal idempotents summing to the identity. For real $x_0,\ldots,x_n$ and $\Lambda(x)=\sum_jx_jE_j$,
--   $$\Gamma_B(\Lambda(x))=\sum_i\Upsilon_i\sum_jM_{ij}x_j,\qquad\operatorname{Tr}_BE_j=g_jI_{A'},$$
--   where
--   $$M_{ij}=2^{-n}\sum_{k=\max(0,j-(n-i))}^{\min(i,j)}\binom{n-i}{j-k}\binom ik(1+d)^{i-k}(1-d)^k,\quad g_j=2^{-n}\binom nj(d+1)^{n-j}(d-1)^j.$$
--   For any selected NS/PPTp flags, every primal feasible $(\rho,\Lambda)$ for $(\mathcal W^{(d,\alpha)})^{\otimes n}$ has a feasible pair $(I/d^n,\Lambda(x))$ with the identical full-transpose Choi objective. This is the lossless symmetry reduction, with the remaining identity on the input system.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 13, Appendix A (A1)–(A3): symmetry reduction coefficients

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)

open QAlgorithms.Papers.Independent.Information100.P21 (pt)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF pp.13--14, (A1)--(A3): sector orthogonality, exact partial transpose and
partial trace, and lossless averaging to rho=I/d^n and the real wernerSector ansatz.
The printed remaining-system identity is corrected from I_B to I_input. -/
theorem symmetry_reduction_coefficients
    (d n K : ℕ) (hd : 2 ≤ d) (hn : 0 < n) (hK : 0 < K)
    (alpha : ℝ) (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (s p : Bool) :
    (∀ j : Fin (n + 1), sectorSum d n j * sectorSum d n j = sectorSum d n j) ∧
    (∀ i j : Fin (n + 1), i ≠ j → sectorSum d n i * sectorSum d n j = 0) ∧
    (∑ j : Fin (n + 1), sectorSum d n j) = 1 ∧
    (∀ x : Fin (n + 1) → ℝ,
      pt (ansatz d n x) = ∑ i : Fin (n + 1),
        ((∑ j, coeffM d n i j * x j : ℝ) : ℂ) • bellSectorSum d n i (by omega)) ∧
    (∀ j : Fin (n + 1), traceRight (sectorSum d n j) = (coeffG d n j : ℂ) • 1) ∧
    (∀ rho L, Primal K s p rho L →
      ∃ x : Fin (n + 1) → ℝ,
        Primal K s p (((d : ℂ)^n)⁻¹ • 1) (ansatz d n x) ∧
        primalObjective (piSuperop (fun _ : Fin n => wernerHolevoChannel d alpha)) L =
          primalObjective (piSuperop (fun _ : Fin n => wernerHolevoChannel d alpha)) (ansatz d n x)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P11

end
