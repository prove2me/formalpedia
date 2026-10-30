-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P22_eMax_channel_cone
-- name    : QAlgorithms.Papers.Independent.Bridge50.P22.eMax_channel_cone
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:15:51.017994+00:00
-- url     : https://prove2.me/theorems/fec55343-8daa-4776-8a6f-f18ec9407f29
-- title:
--   Attained separable-cone expression for channel Emax
-- statement:
--   Let $\mathcal N_{A\to B}$ be a quantum channel between positive finite-dimensional registers, with a reference $S\simeq A$. Define the unnormalized Choi operator $J^{\mathcal N}_{SB}=(\operatorname{id}_S\otimes\mathcal N)(|\Upsilon\rangle\langle\Upsilon|)$, where $|\Upsilon\rangle=\sum_i|i\rangle_S|i\rangle_A$. Let $E_{\max}(\mathcal N)$ be the largest output max-relative entropy of entanglement over unit pure inputs on $SA$. Then the minimum below is attained, and
--
--   $$E_{\max}(\mathcal N)=\log_2\Sigma(\mathcal N),\qquad \Sigma(\mathcal N)=\min\{\|\operatorname{Tr}_B Y_{SB}\|_\infty:Y_{SB}\in\overrightarrow{\mathrm{SEP}}(S:B),\ J^{\mathcal N}_{SB}\le Y_{SB}\}.$$
--
--   Here $\overrightarrow{\mathrm{SEP}}$ is the unnormalized separable positive cone, the inequality is in Loewner order, and $\|\cdot\|_\infty$ is the spectral operator norm. This supplies the channel counterpart of the state cone expression without any full-rank input restriction.
-- source:
--   Amortization does not enhance the max-Rains information of a quantum channel, arXiv:1709.04907v2, PDF p. 13, Lemma 7 / eqs. (75)–(76)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P22

open QAlgorithms QAlgorithms.Entanglement Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (Le eMax)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pptPrime target)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P04 (IsPPTChannel)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section Statements

variable {A B C D L R : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype L] [Fintype R]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq L] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty L] [Nonempty R]

/-- Lemma 7, PDF pp.13–14, (75)–(76): separable-cone channel expression
with an attained minimum, unnormalized Choi matrix and spectral operator norm.
The proof's temporary invertibility ansatz is not a theorem hypothesis. -/
theorem eMax_channel_cone (N : Superop A B) (hN : IsChannel N) :
    channelEMax N = elog (sigmaSep N) ∧
      IsLeast (channelConeObjectives N) (sigmaSep N) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Bridge50.P22

end
