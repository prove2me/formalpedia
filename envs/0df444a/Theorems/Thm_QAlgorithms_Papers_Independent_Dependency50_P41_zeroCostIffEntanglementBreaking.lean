-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P41_zeroCostIffEntanglementBreaking
-- name    : QAlgorithms.Papers.Independent.Dependency50.P41.zeroCostIffEntanglementBreaking
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:53:10.985957+00:00
-- url     : https://prove2.me/theorems/8c62931f-a91f-497a-839d-f64af0122720
-- title:
--   Zero operational cost characterizes entanglement breaking
-- statement:
--   All systems are finite-dimensional complex Hilbert spaces of positive dimension. Logarithms and entropies are in bits. Let $\mathcal E:A\to B$ be CPTP. The channel cost $E_C(\mathcal E)$ is the infimum of asymptotic LOCC simulation rates: Alice initially holds the entire input and one half of a normalized maximally entangled state of Schmidt rank $M_n$, Bob holds the other half, Alice has no required output, and Bob receives the output. One protocol at each block length approximates the whole channel $\mathcal E^{\otimes n}$ in full diamond norm, with error tending to zero; its rate is $\limsup_n\log_2 M_n/n$. Call $\mathcal E$ entanglement breaking when $(\mathcal E\otimes I_{A^\prime})(\psi)$ is separable for every normalized pure state $\psi$ on $AA^\prime$, where $A^\prime\cong A$. Separability means a finite convex combination of product density matrices. Then $$E_C(\mathcal E)=0\quad\Longleftrightarrow\quad\mathcal E\text{ is entanglement breaking}.$$
--
--   The equivalence covers all positive input and output dimensions.
-- source:
--   Entanglement Cost of Quantum Channels, arXiv:1108.5357v3, PDF p. 13, Corollary 18

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

/-- arXiv:1108.5357v3, PDF p.13, Corollary 18. -/
theorem zeroCostIffEntanglementBreaking {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (E : Superop (Fin a) (Fin b)) (hE : IsChannel E) :
    channelCost E = 0 ↔ EntanglementBreaking ha hb E := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P41

end
