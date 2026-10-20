-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_krausAchievability
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.krausAchievability
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:48:47.181743+00:00
-- url     : https://prove2.me/theorems/50230400-70ee-425c-8a38-589175be0196
-- title:
--   Kraus-family achievability bound
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces of positive dimension. Logarithms and entropies are in bits. Let $\mathcal E:A\to B$ be CPTP. The channel cost $E_C(\mathcal E)$ is the infimum of asymptotic LOCC simulation rates: Alice initially holds the entire input and one half of a normalized maximally entangled state of Schmidt rank $M_n$, Bob holds the other half, Alice has no required output, and Bob receives the output. One protocol at each block length approximates the whole channel $\mathcal E^{\otimes n}$ in full diamond norm, with error tending to zero; its rate is $\limsup_n\log_2 M_n/n$. For any finite Kraus representation $\mathcal E(X)=\sum_kK_kXK_k^\dagger$, with $\sum_kK_k^\dagger K_k=I_A$, and any normalized input $\tau_A$, put $p_k=\operatorname{tr}(K_k\tau_AK_k^\dagger)$ and $\tau_B^k=K_k\tau_AK_k^\dagger/p_k$ when $p_k>0$. Then $$E_C(\mathcal E)\le\inf_{\{K_k\}}\sup_{\tau_A\in\mathcal S(A)}\sum_kp_kH(\tau_B^k).$$ A branch with $p_k=0$ contributes exactly zero and is not normalized.
--
--   The Kraus family is chosen before the worst-case input, yielding a uniform simulation bound.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 7, Lemma 13

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P41

open scoped ComplexConjugate Matrix ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)

open QAlgorithms.Papers.Independent.Information100.P08 (PureEnsemble formation pureAverage)

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC spinFlip concurrence)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy groupedPower)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1108.5357v3, PDF pp.7–9, Lemma 13, (23). -/
theorem krausAchievability {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (E : Superop (Fin a) (Fin b)) (hE : IsChannel E) :
    channelCost E ≤ ⨅ D : KrausDecomposition E, (krausWorstCost D : EReal) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end
