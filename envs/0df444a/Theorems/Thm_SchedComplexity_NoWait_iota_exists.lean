-- Prove2me | Theorems.Thm_SchedComplexity_NoWait_iota_exists
-- name    : SchedComplexity.NoWait.iota_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:14:28.361752+00:00
-- url     : https://prove2.me/theorems/23a9cd2a-2fee-456e-9d6e-3bfdc8f4564b
-- title:
--   Proof of Theorem 5(a) — an admissible ordering ι of the job pairs exists (n ≠ 2)
-- statement:
--   Let $n\ne2$ and $m=n(n-1)+2$. There is a bijection $\iota$ from the ordered pairs $(j,k)$ of distinct jobs $j,k\in\{1,\dots,n\}$ onto the machine indices $\{2,\dots,m-1\}$ such that
--   $$\iota(j,\ell)\ne\iota(\ell,k)+1\qquad\text{for all } j\ne\ell,\ \ell\ne k,$$
--   i.e. "for no $J_\ell$ some $M_{\iota(j,\ell)}$ directly follows an $M_{\iota(\ell,k)}$". The paper says that "such an ordering of the pairs $(j,k)$ can easily be constructed".
--
--   This property makes the partial sums $q_{\ell i}$ of the construction unambiguous and is used in computing the delays $c_{jk}$.
--
--   **Formalization Note** The paper does not exclude $n=2$, but there no such ordering exists: the two pairs $(1,2)$ and $(2,1)$ violate the condition in either order. The statement therefore assumes $n\ne2$ (for $n=0,1$ there are no pairs and the empty assignment works). The reduction of Theorem 5 must treat $n=2$ separately.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 24, proof of Theorem 5(a)

import Mathlib
import Definitions.Def_SchedComplexity_NoWait_Construction

namespace SchedComplexity.NoWait

/-- The ordering `ι` of p. 24 exists for every number of jobs `n ≠ 2`: a bijection from ordered
pairs of distinct jobs onto the machines `2, …, n(n−1)+1` such that no `ι(j,ℓ)` equals
`ι(ℓ,k) + 1`. (For `n = 2` no such ordering exists; the paper says it "can easily be
constructed" without excluding this case.) -/
theorem iota_exists (n : ℕ) (hn : n ≠ 2) : ∃ ι : Fin n → Fin n → ℕ, Admissible n ι := by sorry

end SchedComplexity.NoWait
