-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_depolarizing_formulas
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.depolarizing_formulas
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:46:53.137841+00:00
-- url     : https://prove2.me/theorems/bc0df053-38ec-4010-b4b1-9c09420b73eb
-- title:
--   §5.1, (5.3)–(5.7): depolarizing formulas and norm separation
-- statement:
--   Let $\Omega_\mu(X)=\mu X+(1-\mu)(\operatorname{Tr}X)I_d/d$, where $d\ge1$ and the map is CP: for $d>1$, $-1/(d^2-1)\le\mu\le1$; for $d=1$ any real $\mu$ is allowed. For finite real $p\ge1$, put $\lambda_0=[1+(d^2-1)\mu]/d^2$ and $\lambda_1=(1-\mu)/d^2$. Then
--
--   $$\omega_p(\Omega_\mu)=d^{-(p+1)/p}\big[(1-\mu+d^2\mu)^p+(d^2-1)(1-\mu)^p\big]^{1/p},$$
--   $$S_{\mathrm{CB,min}}(\Omega_\mu)=S(X_{\Omega_\mu}/d)-\log d=-\lambda_0\log\lambda_0-(d^2-1)\lambda_1\log\lambda_1-\log d.$$
--
--   The normalized maximally entangled input attains both the entropy minimum and the norm ratio supremum; its output is unitarily diagonalizable with eigenvalues $\lambda_0$ once and $\lambda_1$ with multiplicity $d^2-1$. For $d=2$, the CB norm equals $\omega_p=2^{-(p+1)/p}[(1+3\mu)^p+3(1-\mu)^p]^{1/p}$, while the induced $1\to p$ norm is $\nu_p=\frac12[(1+\mu)^p+(1-\mu)^p]^{1/p}$. For $\mu>0$ and $p>1$, the CB norm is strictly larger. For qubits, the entropy is nonincreasing as $\mu$ runs from zero to one. Zero logarithmic terms contribute zero. The normalized Choi entropy and distinguished eigenvalue correct the printed (5.3) and first line of (5.5), as forced by the source's spectrum. These formulas exhibit norm separation on explicit channels.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 23, §5.1, (5.3)–(5.7): depolarizing formulas and norm separation

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P16

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal Topology

open Filter Set

namespace QAlgorithms.Papers.Independent.Advance50.P16

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact frozen counterparts; their bodies and conventions were checked for this repair.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms.Papers.Independent.Dependency50.P19 (flip)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Support50.P11 (wernerHolevoChannel)

/-- (5.3)–(5.7), PDF p.23. Printed (5.3) has a norm in place of entropy and
unnormalized Choi entropy; changed to entropy of normalized Choi minus log d.
Printed (5.5) duplicates the small eigenvalue; changed to the preceding stated spectrum.
Strict separation is restricted to p>1, as equality holds at p=1. -/
theorem depolarizing_formulas (d : ℕ) [NeZero d] (mu p : ℝ) (hp : 1 ≤ p)
    (hmu : d = 1 ∨ (-1 / ((d : ℝ)^2-1) ≤ mu ∧ mu ≤ 1)) :
    let N := depolarizing d (1-mu)
    let l0 := (1 + ((d : ℝ)^2-1)*mu) / (d : ℝ)^2
    let l1 := (1-mu) / (d : ℝ)^2
    cbOmega (ENNReal.ofReal p) N = (d : ℝ) ^ (-(p+1)/p) *
      (((1-mu+(d : ℝ)^2*mu)^p + ((d : ℝ)^2-1)*(1-mu)^p) ^ (1/p)) ∧
    minCBEntropy N = entropy (((d : ℂ)⁻¹) • choi N) - Real.log d ∧
    minCBEntropy N = -l0*Real.log l0 - ((d : ℝ)^2-1)*l1*Real.log l1 - Real.log d ∧
    minCBEntropy N = conditionalAt N (finiteMaxEntangled (Fin d)) ∧
    pureRatio (ENNReal.ofReal p) N (finiteMaxEntangled (Fin d)) = cbOmega (ENNReal.ofReal p) N ∧
    (∃ U : Matrix.unitaryGroup (Fin d × Fin d) ℂ,
      idTensorSuperop N (pureDensity (finiteMaxEntangled (Fin d))) =
        (U : Mat (Fin d × Fin d)) *
          Matrix.diagonal (fun j : Fin d × Fin d => ((if j = (0,0) then l0 else l1 : ℝ) : ℂ)) *
            (U : Mat (Fin d × Fin d))ᴴ) ∧
    (d = 2 → inducedSize 1 (ENNReal.ofReal p) N = ENNReal.ofReal
      ((1/2 : ℝ) * (((1+mu)^p + (1-mu)^p) ^ (1/p))) ∧
      cbSize 1 (ENNReal.ofReal p) N = ENNReal.ofReal
        ((2 : ℝ) ^ (-(p+1)/p) * (((1+3*mu)^p+3*(1-mu)^p) ^ (1/p))) ∧
      (0 < mu → 1 < p → inducedSize 1 (ENNReal.ofReal p) N < cbSize 1 (ENNReal.ofReal p) N) ∧
      AntitoneOn (fun t : ℝ => minCBEntropy (depolarizing 2 (1-t))) (Icc 0 1)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
