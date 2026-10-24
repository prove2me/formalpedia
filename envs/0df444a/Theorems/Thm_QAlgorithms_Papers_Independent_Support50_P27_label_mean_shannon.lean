-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P27_label_mean_shannon
-- name    : QAlgorithms.Papers.Independent.Support50.P27.label_mean_shannon
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:10:00.452065+00:00
-- url     : https://prove2.me/theorems/adb3025f-34da-4724-8b19-22815413d855
-- title:
--   Lemma 1: label-versus-mean Shannon distinguishability
-- statement:
--   Let $m\ge0$, and let $\{q_x,\rho_x\}_{x=1}^{2^m}$ be an ensemble of density operators on a finite dimensional nonzero Hilbert space. Thus $q_x\ge0$, $\sum_xq_x=1$, and every $\rho_x$ is positive semidefinite with trace one, including at zero-weight labels. Write $\bar\rho=\sum_xq_x\rho_x$. Let $I_{\mathrm{acc}}$ be the supremum, over finite POVMs, of the mutual information in bits between the ensemble label and the measurement outcome. Let $\operatorname{SD}(\rho,\sigma)$ denote accessible information of the equiprobable binary ensemble consisting of $\rho$ and $\sigma$. Then
--
--   $$
--   \forall x,\qquad q_x\operatorname{SD}(\rho_x,\bar\rho)\le I_{\mathrm{acc}}(\{q_x,\rho_x\}).
--   $$
--
--   The estimate relates a single label's distinguishability from the ensemble mean to the information available from the whole ensemble. No strictly positive weight assumption is imposed.
-- source:
--   The Universal Composable Security of Quantum Key Distribution, arXiv:quant-ph/0409078v1, PDF p. 12, Lemma 1: label-versus-mean Shannon distinguishability

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P27

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P27

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)

open QAlgorithms.Papers.Independent.Dependency50.P24 (Key)

open QAlgorithms.Papers.Independent.Dependency50.P47 (cqMatrix)

attribute [local instance] Classical.decEq Classical.propDecidable

/-- PDF p.12, Lemma 1: any label's weighted Shannon distinguishability from
the ensemble mean is at most accessible information. Zero label weights and
m=0 are allowed; all conditional states are normalized density matrices. -/
theorem label_mean_shannon {m : ℕ} {E : Type} [Fintype E] [Nonempty E]
    (A : CQData (Fin (2 ^ m)) E) (hA : A.Valid) :
    ∀ x, A.prob x * shannonDistinguishability (A.state x) (ensembleMean A) ≤
      accessibleInformation A := by sorry

end QAlgorithms.Papers.Independent.Support50.P27

end
