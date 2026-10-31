-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_entanglement_faithful
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.entanglement_faithful
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:17:02.805765+00:00
-- url     : https://prove2.me/theorems/784f03b2-4cc2-43b1-8cea-fafa80bc8446
-- title:
--   Corollary II.2: faithfulness of regularized relative entropy of entanglement
-- statement:
--   Let there be finitely many, at least one, parties with nonzero finite-dimensional local spaces $H_j$, and let $\rho\in\mathcal D(H_1\otimes\cdots\otimes H_k)$. At blocklength $n\ge1$, let $S_n$ consist of all finite convex combinations of products of normalized states on the grouped local blocks $H_j^{\otimes n}$. Local states may correlate a party's copies. Write $E_R^\infty(\rho)=\inf_{n\ge1}\inf_{\omega\in S_n}D_2(\rho^{\otimes n}\Vert\omega)/n$, with base-two relative entropy and the support convention $D_2=+\infty$ when support inclusion fails.
--
--   If $\rho$ is entangled, meaning it lies outside the fully separable set at one copy, then
--   $$
--   E_R^\infty(\rho)>0.
--   $$
--
--   Strict positivity applies to every entangled state, including mixed multipartite and bound-entangled states.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 6, Corollary II.2: faithfulness of regularized relative entropy of entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6 Corollary II.2 Eq.(17): strict positivity on EVERY entangled state. -/
theorem entanglement_faithful {P : Type} [Fintype P] [DecidableEq P] [Nonempty P]
    (d : P → ℕ) (hd : ∀ j, 0 < d j)
    (rho : Mat (PartyReg d)) (hrho : MultipartiteEntangled d rho) :
    0 < regularizedSetEntropy (separableFamily d) rho := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
