-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P17_learning_replicas
-- name    : QAlgorithms.Papers.Independent.Claimed50.P17.learning_replicas
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:02:11.953804+00:00
-- url     : https://prove2.me/theorems/8400c791-d079-42c5-b54a-9a62342f81e4
-- title:
--   Explicit optimal-learning replica family for d at least three
-- statement:
--   Let $d\ge3$ and let $U$ orient the unknown labeled rank-one measurement $E_i=U|i\rangle\langle i|U^\dagger$. Let $R_\star$ be the one-use learning instrument obtained from the concrete optimal blocks in Eqs.(73),(76), including $s_{xyy}^\alpha=\sigma_zs_{xyx}^\alpha\sigma_z$ and $a=(d+1)/(18d(d-1))$. With the unnormalized Choi convention, its replicas are $G_{ij}(U)=[R_{\star,ij}*E(U)]^T$.
--
--   Write $P^\pm=(I\pm\operatorname{SWAP}_{AB})/2$, let $I$ in each tensor product below act on $B$, and put
--   $$Q'_{\pm}=\frac{P^+\pm3P^-}{\sqrt{9d(d-1)}}.$$
--   Then the complete replicated POVM is
--   $$G_{ii}=\frac{16d-2}{9d(d^2-1)}P^+(E_i\otimes I)P^++\frac{d^2-3}{d(d^2-1)}P^+,$$
--   $$\begin{aligned}G_{ij}={}&\frac{Q'_+(E_i\otimes I)Q'_++Q'_-(E_j\otimes I)Q'_-}{d-1}\\&+\frac{2P^-((E_i+E_j)\otimes I)P^-}{d(d-1)^2(d-2)}+\frac{d-3}{(d-1)^2(d-2)}P^-\qquad(i\ne j).\end{aligned}$$
--   The instrument is feasible for learning and attains Haar score $(9d^2+16d-17)/(6d^2(d^2-1))$. This gives the individual effects of the optimal learned measurement for the dimension range in which the displayed denominators are defined.
--
--   **Formalization Note** The plan's proposed $d=3$ counterexample had an arithmetic error: the printed formula has diagonal target overlap $25/54$, rather than $8/27$. Together with off-diagonal target overlap $17/108$, its score is $7/27$, in agreement with Eq.(78). The full expression also matches the concrete block contraction term by term. The plan file is left unchanged; this drafting decision is recorded for independent moderation.
-- source:
--   Cloning of a quantum measurement, arXiv:1103.5709v2, PDF p. 9, §VI, unnumbered optimal-learning replica formula after Eq.(78)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

open MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P17

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P34 (permutationMatrix)

/-- arXiv:1103.5709v2 PDF p.9, unnumbered formula after Eq.(78).
The source formula is consistent with the concrete optimal-learning blocks.
Plan override: its proposed d=3 diagonal overlap 8/27 was an arithmetic error;
the printed diagonal overlap is 25/54, so the complete haarReplicationScore is 7/27. -/
theorem learning_replicas (d : ℕ) (hd : 3 ≤ d) :
    let R := expandBlocks d (learningBlocks d (learningParameter d))
    IsReplicationStrategy .learning R ∧ haarReplicationScore R = learningValue d ∧
    ∀ U : (Matrix.unitaryGroup (Fin d) ℂ), ∀ i j, replica R U i j = learningReplicaFormula U i j := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P17

end
