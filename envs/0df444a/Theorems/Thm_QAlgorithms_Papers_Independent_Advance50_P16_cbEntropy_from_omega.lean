-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_cbEntropy_from_omega
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.cbEntropy_from_omega
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:28:51.693129+00:00
-- url     : https://prove2.me/theorems/ffa6f9c9-df2c-43e0-b696-58a617953e87
-- title:
--   Theorem 2: entropy from omega_p
-- statement:
--   Let $\Phi:M_m\to M_n$ be any CPT map, with $m,n\ge1$. For $p\ge1$, let $\omega_p(\Phi)$ be the supremum over unit vectors $\psi\in\mathbb C^m\otimes\mathbb C^m$ of the Schatten norm ratio $\|(\mathrm{id}\otimes\Phi)(|\psi\rangle\langle\psi|)\|_p/\|\operatorname{Tr}_2|\psi\rangle\langle\psi|\|_p$. With the minimal CB entropy defined by the same pure-input conditional-entropy infimum, one has
--
--   $$S_{\mathrm{CB,min}}(\Phi)=\lim_{p\downarrow1}\frac{1-\omega_p(\Phi)^p}{p-1}.$$
--
--   Entropy is in nats. This identifies CB entropy with a right-hand limit of channel norms.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 7, Theorem 2: entropy from omega_p

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

/-- Theorem 2 / (2.10), PDF pp.7–8: p is a real approaching one strictly from above;
the power p is outside cbOmega. Natural logarithms fix the limit's units. -/
theorem cbEntropy_from_omega {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (Phi : (Mat I →ₗ[ℂ] Mat J)) (hPhi : IsChannel Phi) :
    Tendsto (fun p : ℝ => (1 - (cbOmega (ENNReal.ofReal p) Phi) ^ p) / (p-1))
      (𝓝[>] 1) (𝓝 (minCBEntropy Phi)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
