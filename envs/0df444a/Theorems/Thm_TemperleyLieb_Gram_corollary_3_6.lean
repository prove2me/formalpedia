-- Prove2me | Theorems.Thm_TemperleyLieb_Gram_corollary_3_6
-- name    : TemperleyLieb.Gram.corollary_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:52.008403+00:00
-- url     : https://prove2.me/theorems/52c0be37-d75f-4a41-b6ae-02e1dee92307
-- title:
--   Corollary 3.6, p. 15 — triangular Jucys–Murphy action
-- statement:
--   For every positive $n$, the Murphy cellular basis admits a Jucys–Murphy family whose $k$th operator is the explicitly defined $T_k$ and whose content on a tableau $t$ is the polynomial $r_t(k)$:
--
--   $$m_tT_k\equiv r_t(k)m_t+\sum_{v\triangleright t}a_vm_v\pmod{\check A_n^\lambda},\qquad 0\le k\le n.$$
--
--   The family is commuting and fixed by the cellular anti-involution, as established in §3. This triangular action ties the combinatorial path to the operator eigenvalues used in the spectral projectors.
--
--   **Formalization Note** The published `JMFamily` packages the congruence with coefficients independent of the row tableau, as well as commutation and fixedness. The theorem asserts existence of both it and the Murphy datum.
-- source:
--   Enyang, Representations of Temperley–Lieb Algebras, arXiv:0710.3218v1, p. 15, Corollary 3.6; pp. 10–12, Lemma 3.1 and the commuting-family statement

import Mathlib
import Definitions.Def_TemperleyLieb_Gram_Models

namespace TemperleyLieb.Gram
open QAlgorithms.Papers.Independent.Support21.P08

/-- Enyang, Corollary 3.6, p. 15, with the adjacent commuting and fixedness
claims packaged in `JMFamily`. The datum is asserted to exist. -/
theorem corollary_3_6 (n : ℕ) (hn : 1 ≤ n) :
    ∃ D : RDatum n, IsMurphyDatum R Polynomial.X n D ∧
      ∃ J : JMFamily D (n + 1),
        (∀ k : Fin (n + 1), J.L k = JM R Polynomial.X n k) ∧
        (∀ (f : Fin (n / 2 + 1)) (t : Tab n f) (k : Fin (n + 1)),
          J.content ⟨f, t⟩ k = r t k) := by sorry

end TemperleyLieb.Gram
