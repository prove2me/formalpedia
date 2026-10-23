-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P20_erasureHolevo
-- name    : QAlgorithms.Papers.Independent.Claimed50.P20.erasureHolevo
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T11:26:50.811643+00:00
-- url     : https://prove2.me/theorems/0f0e8323-972a-4d6a-99db-56cdfd3974de
-- title:
--   Lemma 3 (Bennett et al. [4]): Holevo information of qubit erasure
-- statement:
--   Let $\epsilon\in[0,1]$ and let $\mathcal N_\epsilon$ be the normalized qubit-to-qutrit erasure channel, with orthogonal flag and erasure probability $\epsilon$. Let $\chi(\mathcal N)$ denote the supremum over all finite normalized input ensembles, including mixed inputs, of $H(\sum_xp_x\mathcal N(\rho_x))-\sum_xp_xH(\mathcal N(\rho_x))$, in bits. Then
--
--   $$\chi(\mathcal N_\epsilon)=1-\epsilon.$$
--
--   The maximum is attained by a finite normalized ensemble. This is a one-shot Holevo-information identity, including the fully erased and noiseless endpoints. It is the explicitly inventoried Bennett et al. result, reproved on the source's pp.19--20.
-- source:
--   The quantum dynamic capacity formula of a quantum channel, arXiv:1004.0458v3, PDF p. 19, Lemma 3 (Bennett et al. [4]): Holevo information of qubit erasure

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P20

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P20

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble PureEnsemble channelHolevo)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Dependency50.P23 (IsHadamard)

open QAlgorithms.Papers.Independent.Dependency50.P41 (qubitErasure)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 3 (Bennett et al.), PDF pp.19--20: ordinary one-shot Holevo information. -/
theorem erasureHolevo (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1) :
    channelHolevo (qubitErasure epsilon) = 1 - epsilon ∧
      IsGreatest {v | ∃ e : Ensemble (Fin 2),
        v = QAlgorithms.Papers.Independent.Information100.P08.outputHolevo (qubitErasure epsilon) e}
        (1 - epsilon) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P20

end
