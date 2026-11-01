-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P97_bound_monotonicity
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P97.bound_monotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:55:50.296234+00:00
-- url     : https://prove2.me/theorems/a06dfc9a-1a10-4071-88a0-cc1e669dddff
-- title:
--   Monotonicity and endpoints of the ancillary-overlap lower bound
-- statement:
--   Fix $0\le f<1$ and positive integers $N,M$, and set $L=N+M$. Define the scalar function
--
--   $$B_{N,M}(f,\phi)=f^N\phi-\frac{f^L\sqrt{1-f^{2N}\phi^2}}{\sqrt{1-f^{2L}}}.$$
--
--   This function is nondecreasing on $[f^M,1]$, and its minimum and maximum occur at the endpoints:
--
--   $$B_{N,M}(f,f^M)=0,\qquad 0\le B_{N,M}(f,\phi)\le B_{N,M}(f,1)\quad(f^M\le\phi\le1).$$
--
--   For one original and one additional copy, the maximum has the explicit value
--
--   $$B_{1,1}(f,1)=f-\frac{f^2}{\sqrt{1+f^2}}.$$
--
--   This describes the scalar lower bound as ancillary overlap varies; it makes no attainability assertion about an arbitrary device.
-- source:
--   Lower bound on the relative error of mixed-state cloning and related operations, arXiv:quant-ph/0208159v2, PDF p. 4, §IV, paragraphs after Eqs. (21) and (23)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P97

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P97

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity sineDistance receiverChannel)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

/-- PDF p.4, paragraphs after Eqs. (21) and (23). The scalar bound is
nondecreasing (constant zero for `f=0`), with the stated endpoint minimum
and maximum. This is not an attainability assertion about arbitrary cloners. -/
theorem bound_monotonicity {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f < 1) :
    MonotoneOn (cloningBound N M f) (Set.Icc (f ^ M) 1) ∧
    cloningBound N M f (f ^ M) = 0 ∧
    (∀ phi ∈ Set.Icc (f ^ M) 1,
      0 ≤ cloningBound N M f phi ∧ cloningBound N M f phi ≤ cloningBound N M f 1) ∧
    cloningBound 1 1 f 1 = standardBound f := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P97

end
