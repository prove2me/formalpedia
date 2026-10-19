-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_wernerThreshold
-- name    : QAlgorithms.Papers.Independent.Information100.P04.wernerThreshold
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:33:38.164982+00:00
-- url     : https://prove2.me/theorems/0487c4df-e8e9-41d2-94ad-eff55dc216d9
-- title:
--   Werner threshold effects and their achievable rate
-- statement:
--   Let $d\ge2$, $u=(d-1)/(d+1)$, $q=d/(d+1)$, and $A=P_1+uP_0$, where $P_0,P_1$ are the symmetric and antisymmetric Werner projections. For the Werner state $\rho_p$ with antisymmetric weight $p\in(1/2,1]$,
--
--   $$E_{d,\mathrm{PPT}}(\rho_p)\ge D_{\rm bin}\!\left(\frac{d-1+2p}{d+1}\middle\|\frac d{d+1}\right).$$
--
--   For $p=1/2+\delta$, this fixed achievable curve equals $2\delta^2/(d\ln2)+O(\delta^3)$ as $\delta\downarrow0$; the implied constant and neighborhood may depend on $d$. For integers $0\le k\le n$, let $Q_{n,k}=\sum_{x\in\{0,1\}^n:|x|\ge k}\bigotimes_j(A\text{ if }x_j=1;\ I-A\text{ otherwise})$. This is an effect, $Q_{n,0}=I$, and $Q_{n,k}^\Gamma\ge0$. On the sector with $i$ antisymmetric factors its scalar coefficient is $\Pr\{\operatorname{Bin}(n-i,u)\ge k-i\}$, with a nonpositive threshold interpreted as zero required successes. On the transposed sector with $l$ Bell factors its eigenvalue is $\Pr\{\operatorname{Bin}(n-l,q)\ge k\}$, which is nonnegative and at most the $l=0$ value. In particular $\|Q_{n,k}^\Gamma\|_\infty=\Pr\{\operatorname{Bin}(n,q)\ge k\}$. These exact sector identities handle the signed Werner transform.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 27, eq121-123

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Eqs.(121)–(123), PDF p.27: the operational lower bound, its quadratic expansion,
and the exact physical and transposed sectors of every threshold effect. -/
theorem wernerThreshold (d : ℕ) (hd : 2 ≤ d) :
    (∀ p : ℝ, 1/2 < p → p ≤ 1 →
      binaryD (((d:ℝ)-1+2*p)/(d+1)) (wernerQ d) ≤ distillable (werner d p)) ∧
    (∃ C > (0:ℝ), ∃ eps > (0:ℝ), ∀ delta : ℝ, 0 < delta → delta < eps →
      |binaryD (((d:ℝ)-1+2*(1/2+delta))/(d+1)) (wernerQ d) -
        (2/((d:ℝ)*Real.log 2))*delta^2| ≤ C*delta^3) ∧
    (∀ n k : ℕ, k ≤ n → IsEffect (thresholdEffect d n k) ∧
      (gamma (thresholdEffect d n k)).PosSemidef ∧
      thresholdEffect d n 0 = 1 ∧
      specNorm (gamma (thresholdEffect d n k)) = binomialTail n k (wernerQ d) ∧
      (∀ i : ℕ, i ≤ n →
        thresholdEffect d n k * typeProjector (wernerP0 d) (wernerP1 d) n i =
          (binomialTail (n-i) (k-i) (wernerU d) : ℂ) •
            typeProjector (wernerP0 d) (wernerP1 d) n i) ∧
      (∀ l : ℕ, l ≤ n →
        gamma (thresholdEffect d n k) * typeProjector (1-bellProjector d) (bellProjector d) n l =
          (binomialTail (n-l) k (wernerQ d) : ℂ) •
            typeProjector (1-bellProjector d) (bellProjector d) n l ∧
        0 ≤ binomialTail (n-l) k (wernerQ d) ∧
        binomialTail (n-l) k (wernerQ d) ≤ binomialTail n k (wernerQ d))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
