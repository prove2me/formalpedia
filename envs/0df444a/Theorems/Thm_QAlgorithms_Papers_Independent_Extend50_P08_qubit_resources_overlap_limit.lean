-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_qubit_resources_overlap_limit
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.qubit_resources_overlap_limit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:29:11.175565+00:00
-- url     : https://prove2.me/theorems/3eb7bcb2-a161-461d-9f98-139b23c94f71
-- title:
--   Qubit resource overlap identity and limit
-- statement:
--   Let $N\ge1$. For qubit Young diagrams use the principal vector $v_\mu=2\sin(\pi(\mu_1-\mu_2+1)/(N+2))/\sqrt{N+2}$ and the canonical optimal probabilistic and deterministic filters of (A5),(A9). Their root fidelity $R_N$ satisfies
--
--   $$R_N=\frac{2}{N+2}\sqrt{\frac6{(N+1)(N+3)}}\sum_{k=0}^{\lfloor N/2\rfloor}(N-2k+1)\sin\!\left(\frac{\pi(N-2k+1)}{N+2}\right),\qquad R_N\longrightarrow\frac{\sqrt6}{\pi}.$$
--
--   Here $k=N/2-j$ reindexes the parity-respecting source spin set. The stated vector is a nonnegative unit principal vector. The full lemma’s unrestricted maximum clause is separately deferred; this item records exactly its identity and limit subresult.
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 15, Lemma 8, Eq.(56) and limit clause: qubit optimal-resource overlap

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 8, PDF pp.15–16 Eq.(56) and its limit clause only.
The unrestricted rounded-decimal maximum is separately deferred. -/
theorem qubit_resources_overlap_limit :
    (∀ N : ℕ, 0 < N → IsPrincipal (qubitPrincipal N) ∧
      qubitResourceOverlap N = qubitOverlapFormula N) ∧
    Filter.Tendsto qubitResourceOverlap Filter.atTop (nhds (Real.sqrt 6 / Real.pi)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
