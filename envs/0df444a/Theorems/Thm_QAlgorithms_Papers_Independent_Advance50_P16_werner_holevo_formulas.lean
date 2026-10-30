-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_werner_holevo_formulas
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.werner_holevo_formulas
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:47:43.231182+00:00
-- url     : https://prove2.me/theorems/5c0ee513-be32-4afd-871d-596699ba6032
-- title:
--   §5.1, (5.8): Werner–Holevo entropy and norm formulas
-- statement:
--   Let $d\ge2$ and let $\Phi_{\mathrm{WH}}(X)=[(\operatorname{Tr}X)I_d-X^T]/(d-1)$. For every normalized pure input, its output $\gamma_{12}=(\mathrm{id}_d\otimes\Phi_{\mathrm{WH}})(|\psi\rangle\langle\psi|)$ and input reference marginal $\gamma_1$ satisfy
--
--   $$S(\gamma_{12})-S(\gamma_1)\ge\log\frac{d-1}{2},\qquad S_{\mathrm{CB,min}}(\Phi_{\mathrm{WH}})=\log\frac{d-1}{2}.$$
--
--   The entropy minimum is attained by the normalized maximally entangled vector. For every $1\le p\le\infty$, taking $1/\infty=0$,
--
--   $$\omega_p(\Phi_{\mathrm{WH}})=\left(\frac2{d-1}\right)^{1-1/p},\qquad
--   \nu_p(\Phi_{\mathrm{WH}})=\left(\frac1{d-1}\right)^{1-1/p}.$$
--
--   The same maximally entangled vector attains $\omega_p$, and the first norm is strictly larger when $p>1$. All entropies are in nats, so $d=2$ gives $-\log2$ and $d=3$ gives zero. This is the explicit WH entropy and norm example of (5.8).
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 24, §5.1, (5.8): Werner–Holevo entropy and norm formulas

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

/-- (5.8), PDF p.24: the WH channel, entropy bound and maximally entangled
optimizer. Natural-log d=2 value is -log 2, rather than the printed -1 bits.
The strict norm separation requires p>1; p=1 gives equality. -/
theorem werner_holevo_formulas (d : ℕ) [NeZero d] (hd : 2 ≤ d) (p : ℝ≥0∞) (hp : 1 ≤ p) :
    let N := wernerHolevoChannel d 1
    (∀ psi : EuclideanSpace ℂ (Fin d × Fin d), ‖psi‖ = 1 →
      conditionalAt N psi ≥ Real.log (((d : ℝ)-1)/2)) ∧
    minCBEntropy N = Real.log (((d : ℝ)-1)/2) ∧
    conditionalAt N (finiteMaxEntangled (Fin d)) = minCBEntropy N ∧
    cbOmega p N = (2/((d : ℝ)-1)) ^ (1-recip p) ∧
    pureRatio p N (finiteMaxEntangled (Fin d)) = cbOmega p N ∧
    inducedSize 1 p N = ENNReal.ofReal ((1/((d : ℝ)-1)) ^ (1-recip p)) ∧
    (1 < p → ((1/((d : ℝ)-1)) ^ (1-recip p)) < cbOmega p N) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
