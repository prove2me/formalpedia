-- Prove2me | Theorems.Thm_Rado_rado_defect_le
-- name    : Rado.rado_defect_le
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:29:41.169138+00:00
-- url     : https://prove2.me/theorems/e1e387a8-09a6-45f5-8f52-53b72fe3da8a
-- title:
--   Rado's theorem: weak duality for independent partial transversals
-- statement:
--   Let $k$ be a field, $V$ a $k$-vector space, $\iota$ a finite index set, and $(A_i)_{i\in\iota}$ a family of finite subsets of $V$. For $S\subseteq\iota$ write $A(S)=\bigcup_{i\in S}A_i$. A *partial transversal* is a choice of vectors $v_j\in A_j$ for the indices $j$ in a subset $J\subseteq\iota$; it is *independent* if $(v_j)_{j\in J}$ is linearly independent over $k$. A *transversal* is a choice $v_i\in A_i$ for every $i\in\iota$.
--
--   If $(v_j)_{j\in J}$ is an independent partial transversal, then for every $S\subseteq\iota$
--
--   $$|J|\le|\iota\setminus S|+\dim_k\operatorname{span}A(S).$$
--
--   This is the easy half of Rado's theorem (the matroid analogue of the trivial direction of Hall's theorem).
--
--   **Formalization Note.** Each $A_i$ is assumed finite so that the dimensions are finite; `LinearIndepOn k v J` is linear independence of the family $v$ restricted to $J$, and `Sᶜ` is the complement of `S` in the finite index type.
-- source:
--   R. Rado, A theorem on independence relations, Quart. J. Math. Oxford 13 (1942), 83-89

import Mathlib

namespace Rado

theorem rado_defect_le {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    [DecidableEq ι] (A : ι → Set V) (hA : ∀ i, (A i).Finite)
    (J : Finset ι) (v : ι → V) (hv : ∀ j ∈ J, v j ∈ A j) (hind : LinearIndepOn k v (J : Set ι))
    (S : Finset ι) :
    J.card ≤ Sᶜ.card + Module.finrank k (Submodule.span k (⋃ i ∈ S, A i)) := by sorry

end Rado
