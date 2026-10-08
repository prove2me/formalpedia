-- Prove2me | Theorems.Thm_Rado_rado_hall
-- name    : Rado.rado_hall
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:29:32.268447+00:00
-- url     : https://prove2.me/theorems/a6b00c06-9182-4eb7-b6b0-81ebd9124444
-- title:
--   Rado's theorem (Hall form): independent transversals
-- statement:
--   Let $k$ be a field, $V$ a $k$-vector space, $\iota$ a finite index set, and $(A_i)_{i\in\iota}$ a family of finite subsets of $V$. For $S\subseteq\iota$ write $A(S)=\bigcup_{i\in S}A_i$. A *partial transversal* is a choice of vectors $v_j\in A_j$ for the indices $j$ in a subset $J\subseteq\iota$; it is *independent* if $(v_j)_{j\in J}$ is linearly independent over $k$. A *transversal* is a choice $v_i\in A_i$ for every $i\in\iota$.
--
--   If
--
--   $$|S|\le\dim_k\operatorname{span}A(S)\qquad\text{for every }S\subseteq\iota,$$
--
--   then there is a transversal $(v_i)_{i\in\iota}$, $v_i\in A_i$, that is linearly independent. The condition is also necessary (weak duality with $J=\iota$). For $A_i\subseteq\{e_1,\dots,e_n\}$ in a standard basis this is Hall's marriage theorem.
--
--   **Formalization Note.** Only the sufficiency direction is stated; necessity is `Rado.rado_defect_le` with `J = univ`.
-- source:
--   R. Rado, A theorem on independence relations, Quart. J. Math. Oxford 13 (1942), 83-89

import Mathlib

namespace Rado

theorem rado_hall {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    [DecidableEq ι] (A : ι → Set V) (hA : ∀ i, (A i).Finite)
    (h : ∀ S : Finset ι, S.card ≤ Module.finrank k (Submodule.span k (⋃ i ∈ S, A i))) :
    ∃ v : ι → V, (∀ i, v i ∈ A i) ∧ LinearIndependent k v := by sorry

end Rado
