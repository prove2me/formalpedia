-- Prove2me | Theorems.Thm_SignSymRat_Hierarchy_lemma_4_2
-- name    : SignSymRat.Hierarchy.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:07:35.341977+00:00
-- url     : https://prove2.me/theorems/2ac451d5-45d4-4124-a7b8-3d58d6da5b0b
-- title:
--   Lemma 4.2 — invariance under sign symmetries
-- statement:
--   Let $K$ be the feasible set of (SRFO), and let $R_i=R(A_i)$. Under Assumption 1.1 and with at least two ratios, every sign vector $r\in R_i$ preserves the feasible set and the numerator and denominator of ratio $i$:
--
--   $$r(K)=K,\qquad \theta_r(p_i)=p_i,\qquad \theta_r(q_i)=q_i\quad(i\in[N]).$$
--
--   This invariance identifies the symmetries used in the restricted dual and its polynomial averages.
--
--   **Formalization Note** Paper index $1$ is Lean index `0`. The condition $N\ge2$ is explicit because (4.2) otherwise omits the supports of the constraints from $A_1$; the lemma can fail for $N=1$.
-- source:
--   Guo, Wang & Zheng, Exploiting Sign Symmetries in Minimizing Sums of Rational Functions, arXiv:2405.09419v1, p. 10, Lemma 4.2

import Mathlib
import Definitions.Def_SignSymRat_Hierarchy_SignSym

open MvPolynomial

namespace SignSymRat.Hierarchy

/-- Lemma 4.2, p. 10. The paper's i=1 is Lean's index 0. -/
theorem lemma_4_2 {n m N : ℕ} (P : SRFO n m N) [NeZero N]
    (hN : 2 ≤ N) (hA : P.Assumption11) :
    ∀ i : Fin N, ∀ r ∈ signSym (P.Aset i),
      flip r '' P.K = P.K ∧ theta r (P.p i) = P.p i ∧ theta r (P.q i) = P.q i := by sorry

end SignSymRat.Hierarchy
