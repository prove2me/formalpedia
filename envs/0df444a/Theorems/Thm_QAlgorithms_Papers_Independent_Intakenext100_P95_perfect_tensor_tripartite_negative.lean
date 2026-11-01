-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P95_perfect_tensor_tripartite_negative
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P95.perfect_tensor_tripartite_negative
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:46:21.806889+00:00
-- url     : https://prove2.me/theorems/b6008930-5e65-424c-87e2-f9f1bc178d7c
-- title:
--   Strictly negative tripartite information of a perfect tensor
-- statement:
--   Let $\lvert\psi\rangle$ be a normalized perfect tensor state on $2n$ spins of common dimension $v\ge2$. Partition all its legs into four pairwise disjoint sets $A,B,C,D$ satisfying $0<|A|,|B|,|C|,|D|<n$. Write $S_X$ for the von Neumann entropy of the actual reduced state on $X$, using logarithms to base $v$. Then
--
--   $$I_3(A,B,C):=S_A+S_B+S_C-S_{AB}-S_{AC}-S_{BC}+S_{ABC}<0.$$
--
--   This is a strict inequality for the stated perfect tensor state; it does not assert nonpositivity for all tensor-network states.
-- source:
--   Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence, arXiv:1503.06237v2, PDF p. 22, Theorem 4: strictly negative tripartite information of a perfect tensor

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P95

namespace QAlgorithms.Papers.Independent.Intakenext100.P95

open scoped Matrix ComplexConjugate

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF pp.22–23, Theorem 4: strict negativity for a four-part partition of a
normalized perfect tensor state, with every part nonempty and smaller than n. -/
theorem perfect_tensor_tripartite_negative {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (hv : 2 ≤ Fintype.card V) (psi : EuclideanSpace ℂ (Fin (2 * n) → V))
    (hstate : IsState psi) (hperfect : IsPerfect psi)
    (parts : Fin 4 → Finset (Fin (2 * n)))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (parts i) (parts j))
    (hcover : Finset.univ.biUnion parts = Finset.univ)
    (hsizes : ∀ i, 0 < (parts i).card ∧ (parts i).card < n) :
    tripartiteInfo psi (parts 0) (parts 1) (parts 2) < 0 := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P95
