-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P13_unitalQubitUltimateCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P13.unitalQubitUltimateCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:22:28.238765+00:00
-- url     : https://prove2.me/theorems/b82fe3d9-45d5-44ca-8d22-bdce7a586a43
-- title:
--   Ultimate unassisted classical capacity of a unital qubit channel
-- statement:
--   Let $\Phi:M_2(\mathbb C)\to M_2(\mathbb C)$ be a unital completely positive trace-preserving linear map. Let $C_{\mathrm{ult}}(\Phi)$ be its operational classical capacity in nats per use: the supremum of asymptotic message rates achievable by finite-message codes whose uniform-message average error tends to zero, with no prior sender–receiver entanglement. Codewords may be arbitrary density matrices entangled across uses, and the receiver may use a collective POVM on all outputs. Let $\chi^*$ be the finite-ensemble Holevo supremum in nats, allowing mixed inputs and zero weights. Then
--
--   $$
--   C_{\mathrm{ult}}(\Phi)=\chi^*(\Phi),\qquad
--   \lim_{n\to\infty}\frac{1}{n}\chi^*(\Phi^{\otimes n})=\chi^*(\Phi).
--   $$
--
--   The second equality is an ordinary limit. Thus the single-use Holevo quantity gives the ultimate unassisted rate even when arbitrary block codes are allowed.
--
--   **Formalization Note** The accepted operational capacity is measured in bits and is multiplied by $\log2$. The normalized sequence has an unused zero extension at $n=0$.
-- source:
--   Additivity for a class of unital qubit channels, arXiv:quant-ph/0103156v2, PDF p. 4, Remark 2, equations (8)–(9)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Support50.P13

open QAlgorithms.Papers.Independent.Gap48.P03
  (productChannel maximumOutputPNorm holevoQuantity depolarizingNormFactor
    phaseChannel qubitPauli)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

open QAlgorithms.Papers.Independent.Information100.P63 (schatten)

open QAlgorithms.Papers.Independent.Dependency50.P23 (ordinaryClassicalCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- King quant-ph/0103156v2, PDF p.4, Remark 2, (8)-(9).
Operational capacity is not defined by the single-use Holevo quantity.
Both its equality and ordinary convergence of the regularized Holevo sequence
are conclusions; no HSW theorem is assumed as an input hypothesis. -/
theorem unitalQubitUltimateCapacity
    (Phi : Superop (Fin 2) (Fin 2)) (hPhi : IsChannel Phi)
    (hPhiUnital : Phi 1 = 1) :
    ultimateCapacityNats Phi = holevoQuantity Phi ∧
    Tendsto (normalizedHolevoRate Phi) atTop (nhds (holevoQuantity Phi)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P13

end
