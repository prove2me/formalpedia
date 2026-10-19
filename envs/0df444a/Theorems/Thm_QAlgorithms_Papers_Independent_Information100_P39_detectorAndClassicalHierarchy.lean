-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P39_detectorAndClassicalHierarchy
-- name    : QAlgorithms.Papers.Independent.Information100.P39.detectorAndClassicalHierarchy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T11:17:46.841103+00:00
-- url     : https://prove2.me/theorems/52846df1-8ebb-456a-9018-645fd758ef4f
-- title:
--   Unnumbered applications: exact detector models and classical linear codes
-- statement:
--   Let independent binary faults $b\in\mathbb F_2^M$ have arbitrary probabilities in $[0,1]$. Let $D$ and $\Lambda$ be binary-linear maps recording detector events and logical flips. For a classical binary code, let $H$ be any binary parity-check matrix. Define
--
--   $$\Delta_r^{\mathrm{det}}=H_r(D(b),\Lambda(b))-H_r(D(b)),\qquad
--   \Delta_r^{\mathrm{cl}}=H_r(b)-H_r(Hb).$$
--
--   Both quantities are nonincreasing through positive integer orders and the infinite-order endpoint. Entropies use natural logarithms. The detector application requires an exact representation by independent Bernoulli fault mechanisms; it makes no computational-efficiency assertion.
-- source:
--   Hierarchy of Rényi Coherent Information in Stabilizer Codes, arXiv:2609.11930v1, PDF p. 4, Unnumbered applications: exact detector models and classical linear codes

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P39

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF p.4: exact detector models and classical binary parity-check codes. -/
theorem detectorAndClassicalHierarchy {m d l h : ℕ} (p : Fin m → ℝ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (D : Bits m →ₗ[F2] Bits d) (L : Bits m →ₗ[F2] Bits l)
    (H : Matrix (Fin h) (Fin m) F2) :
    DecreasingOrders (fun r =>
      entropy r (pushLaw (binaryLaw p) (fun b => (D b, L b))) -
        entropy r (pushLaw (binaryLaw p) D)) ∧
    DecreasingOrders (fun r => entropy r (binaryLaw p) -
      entropy r (pushLaw (binaryLaw p) (fun b => H.mulVec b))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P39

end
