-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_entangled_conversion_cost_positive
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.entangled_conversion_cost_positive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:17:53.024881+00:00
-- url     : https://prove2.me/theorems/85a03508-8344-487a-9c6c-407f44da4a26
-- title:
--   Corollary II.3: positive LOCC input-copy cost between entangled states
-- statement:
--   Let there be finitely many, at least one, parties with nonzero finite-dimensional local spaces $H_j$, and let $\rho\in\mathcal D(H_1\otimes\cdots\otimes H_k)$. At blocklength $n\ge1$, let $S_n$ consist of all finite convex combinations of products of normalized states on the grouped local blocks $H_j^{\otimes n}$. Local states may correlate a party's copies. Write $E_R^\infty(\rho)=\inf_{n\ge1}\inf_{\omega\in S_n}D_2(\rho^{\otimes n}\Vert\omega)/n$, with base-two relative entropy and the support convention $D_2=+\infty$ when support inclusion fails.
--
--   Let $\sigma$ be another density operator on the same multipartite space, and assume both $\rho$ and $\sigma$ are entangled. Write
--   $$
--   R(\rho\to\sigma)=\inf_{(k_n)}\left\{\limsup_{n\to\infty}\frac{k_n}{n}:\inf_{\Lambda\in\mathrm{LOCC}}\|\Lambda(\rho^{\otimes k_n})-\sigma^{\otimes n}\|_1\longrightarrow0\right\},
--   $$
--   where the optimization uses deterministic trace-preserving LOCC with arbitrary local ancillas and outcome-dependent classical communication, without entanglement assistance. The infimal finite-protocol error is used; no optimum or closedness of LOCC is assumed. An empty feasible set gives $R=+\infty$. Then
--   $$
--   R(\rho\to\sigma)>0.
--   $$
--
--   The rate is input copies per output copy. No asymptotic convertibility hypothesis is added.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 7, Corollary II.3: positive LOCC input-copy cost between entangled states

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

/-- PDF p.7 Corollary II.3 Eq.(19), with cost defined by p.6 Eq.(18): positive
input-copy cost even for inequivalent entangled states; infinity is allowed. -/
theorem entangled_conversion_cost_positive {P : Type} [Fintype P] [DecidableEq P] [Nonempty P]
    (d : P → ℕ) (hd : ∀ j, 0 < d j)
    (rho sigma : Mat (PartyReg d)) (hrho : MultipartiteEntangled d rho) (hsigma : MultipartiteEntangled d sigma) :
    0 < conversionCost d rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
