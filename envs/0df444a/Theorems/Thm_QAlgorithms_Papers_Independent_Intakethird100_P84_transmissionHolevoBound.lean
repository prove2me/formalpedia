-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P84_transmissionHolevoBound
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P84.transmissionHolevoBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:11:34.519081+00:00
-- url     : https://prove2.me/theorems/6ce97148-6f91-4b0a-919b-7cae65fa6d02
-- title:
--   Section 4, printed 3.3: Holevo bound (18)
-- statement:
--   Let $(p_i,D_i)$ be a finite ensemble of normalized densities, with $p_i\ge0$ and $\sum_i p_i=1$. Let $T$ be complex linear, trace preserving and 2-positive, and $(E_j)$ an arbitrary output POVM. Put $D=\sum_i p_iD_i$, $\mu_i(j)=\operatorname{Tr}(T(D_i)E_j)$ and $\mu=\sum_i p_i\mu_i$. With natural entropy,
--
--   $$S(\mu)-\sum_i p_iS(\mu_i)\le S(D)-\sum_i p_iS(D_i).$$
--
--   The averages are computed by the accepted Holevo functional. Singular code states and zero weights are allowed; no average invertibility is required.
-- source:
--   Monotonicity of quantum relative entropy revisited, arXiv:quant-ph/0209053v1, PDF p. 9, Section 4, printed 3.3: Holevo bound (18)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P84

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions, inspected at their recorded source locations.

open QAlgorithms.Papers.Independent.Renew46.P35 (traceAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower marginalAB)

/-- Petz, arXiv:quant-ph/0209053v1, PDF pp.8--9, (18) [10].
Finite transmission ensembles, arbitrary two-positive trace-preserving transmission,
and the actual output POVM. Zero weights and singular code states are allowed.
The accepted Holevo functional computes both averages and uses natural units. -/
theorem transmissionHolevoBound {X I J O : Type*}
    [Fintype X] [Fintype I] [Fintype J] [Fintype O]
    [Nonempty X] [Nonempty I] [Nonempty J] [Nonempty O]
    (p : X → ℝ) (hp : QAlgorithms.Papers.Independent.Information100.P56.IsLaw p)
    (D : X → Matrix I I ℂ) (hD : ∀ i, IsDensityMatrix (D i))
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ)
    (hT : IsTwoPositive T) (htrace : ∀ B, (T B).trace = B.trace)
    (E : O → Matrix J J ℂ) (hE : IsPOVM E) :
    QAlgorithms.Papers.Independent.Information100.P56.holevo p
      (fun i => measurementDensity E (T (D i))) ≤
      QAlgorithms.Papers.Independent.Information100.P56.holevo p D := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P84

end
