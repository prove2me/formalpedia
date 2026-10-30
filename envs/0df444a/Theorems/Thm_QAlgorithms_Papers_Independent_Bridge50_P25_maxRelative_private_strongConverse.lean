-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P25_maxRelative_private_strongConverse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P25.maxRelative_private_strongConverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:01:48.313424+00:00
-- url     : https://prove2.me/theorems/3fa027e4-e298-40b4-a5ea-d57ba2de909d
-- title:
--   Theorem IV.1: strong-converse max-relative-entropy bound
-- statement:
--   Let $T:M_{d_A}\to M_{d_B}$ be a quantum channel in positive finite dimensions. Let $E_{\max}(T)$ be the supremum, over all finite reference systems $R$ and density matrices $\rho_{RA}$, of the minimum of $D_{\max}((\mathrm{id}_R\otimes T)(\rho_{RA})\|\sigma_{RB})$ over separable density matrices $\sigma_{RB}$. All logarithms are in bits. Let $P_{\leftrightarrow}(T)$ be the private-state generation capacity with separable initial state, arbitrary finite local workspaces, unrestricted two-way classical communication, and actual channel uses. Then
--
--   $$P_{\leftrightarrow}(T)\le E_{\max}(T).$$
--
--   Moreover, every sequence of such codes with channel-use counts $m_\nu\to\infty$, key sizes $2^{k_\nu}$, and $k_\nu/m_\nu\to R>E_{\max}(T)$ has half trace-norm error $\epsilon_\nu\to1$ relative to its private-state targets with equal shield dimensions.
--
--   This gives the full strong converse, including error tending to one above the bound.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, PDF p. 14, Theorem IV.1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}

variable [Fintype I] [DecidableEq I] [Nonempty I]

variable [Fintype J] [DecidableEq J] [Nonempty J]

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- Theorem IV.1, PDF pp.14--15: the full private strong converse. -/
theorem maxRelative_private_strongConverse (T : Superop I J) (hT : IsChannel T) :
    PrivateStrongConverseBound T (channelEMax T) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P25

end
