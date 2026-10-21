-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P43_assistedHolevoConverse
-- name    : QAlgorithms.Papers.Independent.Claimed50.P43.assistedHolevoConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:22:16.927616+00:00
-- url     : https://prove2.me/theorems/56eb622a-b3f9-4ecc-be3a-80bd4db1f55e
-- title:
--   Assisted Holevo information is bounded by average-input mutual information
-- statement:
--   Let $\Phi:A\to A'$ be CPTP on nonzero finite-dimensional spaces. Choose a finite probability distribution $(\pi_i)$, one normalized pure shared state $S_{BA}$, and local CPTP encoders $\mathcal E_i$ acting on Alice. Define $S^i_{BA}=(\operatorname{id}_B\otimes\mathcal E_i)(S_{BA})$ and $S_A^i=\operatorname{Tr}_B S^i_{BA}$. Then, in bits,
--
--   $$H\!\left(\sum_i\pi_i(\operatorname{id}_B\otimes\Phi)(S^i_{BA})\right)-\sum_i\pi_i H((\operatorname{id}_B\otimes\Phi)(S^i_{BA}))\le I\!\left(\sum_i\pi_i S_A^i;\Phi\right).$$
--
--   Consequently $C_{\rm ea}^{(1)}(\Phi)\le\max_\rho I(\rho;\Phi)$; for every $n\ge1$ the analogous inequality holds with $\Phi^{\otimes n}$ and all density operators on $A^{\otimes n}$. The encoded marginals are computed from the protocol rather than assumed to satisfy the desired converse.
-- source:
--   On entanglement-assisted classical capacity, arXiv:quant-ph/0106075v2, PDF p. 5, §II, equation (17), with (15),(19): assisted Holevo converse

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P43

noncomputable section

open scoped Matrix ComplexConjugate

open Filter

namespace QAlgorithms.Papers.Independent.Claimed50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45

attribute [local instance] Classical.propDecidable

/-- PDF pp.5--6, (17), (15),(19): the encoded marginal is computed, not a hypothesis.
The one-shot converse and every n-use converse are included. -/
theorem assistedHolevoConverse {A C : Type} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] [Nonempty A] [Nonempty C]
    (N : Superop A C) (hN : IsChannel N) :
    (∀ (m : ℕ) (e : AssistedEnsemble A m), assistedScore N e ≤
      inputMutualInfo N (∑ i, (e.prob i : ℂ) • traceLeft (encodedAssistedState e i))) ∧
    assistedOneShot N ≤ maximalMutualInfo N ∧
    (∀ n : ℕ, 0 < n → assistedOneShot (piSuperop (fun _ : Fin n => N)) ≤
      maximalMutualInfo (piSuperop (fun _ : Fin n => N))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P43

end
