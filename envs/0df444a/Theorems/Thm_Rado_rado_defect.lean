-- Prove2me | Theorems.Thm_Rado_rado_defect
-- name    : Rado.rado_defect
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T13:29:34.929824+00:00
-- url     : https://prove2.me/theorems/d107dbab-9d10-4470-bbe8-72196a43feeb
-- title:
--   Rado's theorem (defect form)
-- statement:
--   Let $k$ be a field, $V$ a $k$-vector space, $\iota$ a finite index set, and $(A_i)_{i\in\iota}$ a family of finite subsets of $V$. For $S\subseteq\iota$ write $A(S)=\bigcup_{i\in S}A_i$. A *partial transversal* is a choice of vectors $v_j\in A_j$ for the indices $j$ in a subset $J\subseteq\iota$; it is *independent* if $(v_j)_{j\in J}$ is linearly independent over $k$. A *transversal* is a choice $v_i\in A_i$ for every $i\in\iota$.
--
--   Then there are an independent partial transversal $(v_j)_{j\in J}$ and a subset $S\subseteq\iota$ with
--
--   $$|J|=|\iota\setminus S|+\dim_k\operatorname{span}A(S).$$
--
--   Together with weak duality this says that the largest size of an independent partial transversal equals $\min_{S\subseteq\iota}\bigl(|\iota\setminus S|+\dim_k\operatorname{span}A(S)\bigr)$. This is Rado's theorem on independent transversals in its defect (min-max) form; for subsets of a basis it is the defect form of Hall's marriage theorem.
--
--   **Formalization Note.** The conclusion is existential in $(J,v,S)$; `LinearIndepOn k v J` is linear independence of $v$ restricted to $J$.
-- source:
--   R. Rado, A theorem on independence relations, Quart. J. Math. Oxford 13 (1942), 83-89

import Mathlib

namespace Rado

theorem rado_defect {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    [DecidableEq ι] (A : ι → Set V) (hA : ∀ i, (A i).Finite) :
    ∃ (J : Finset ι) (v : ι → V) (S : Finset ι),
      (∀ j ∈ J, v j ∈ A j) ∧ LinearIndepOn k v (J : Set ι) ∧
      J.card = Sᶜ.card + Module.finrank k (Submodule.span k (⋃ i ∈ S, A i)) := by sorry

end Rado
