-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P16_ebt_nonnegative_cb_entropy
-- name    : QAlgorithms.Papers.Independent.Advance50.P16.ebt_nonnegative_cb_entropy
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:40:34.006184+00:00
-- url     : https://prove2.me/theorems/5766fe33-c2a7-40c7-9fb2-a2eb711ead60
-- title:
--   Theorem 16: EBT channels have nonnegative CB entropy
-- statement:
--   Let $\Phi:M_m\to M_n$ be an EBT channel between nonzero finite matrix algebras. Then
--
--   $$\omega_p(\Phi)\le1\quad(1\le p\le\infty),\qquad S_{\mathrm{CB,min}}(\Phi)\ge0.$$
--
--   Here $\omega_p$ is the normalized pure-input ratio of (1.6) and the CB entropy uses natural logarithms. The printed word “positive” is read as nonnegative, consistently with the following paragraph and proof: a pure replacement channel has CB entropy zero. This is the valid entropy consequence of entanglement breaking.
-- source:
--   Multiplicativity of completely bounded p-norms implies a new additivity result, arXiv:quant-ph/0506196v2, PDF p. 25, Theorem 16: EBT channels have nonnegative CB entropy

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

/-- Theorem 16, PDF p.25. Printed: entropy is "positive". Changed: nonnegative,
as the following paragraph and proof require; pure replacement channels give equality zero. -/
theorem ebt_nonnegative_cb_entropy {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] [Nonempty J] (Phi : (Mat I →ₗ[ℂ] Mat J)) (hPhi : IsEBT Phi) :
    (∀ p : ℝ≥0∞, 1 ≤ p → cbOmega p Phi ≤ 1) ∧ 0 ≤ minCBEntropy Phi := by sorry

end QAlgorithms.Papers.Independent.Advance50.P16

end
