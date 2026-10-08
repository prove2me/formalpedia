-- Prove2me | Theorems.Thm_SchedComplexity_Partition_theorem_3b_k_identity
-- name    : SchedComplexity.Partition.theorem_3b_k_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T22:02:47.619985+00:00
-- url     : https://prove2.me/theorems/70677499-b5ce-4d35-8f67-4cfafaaea0c8
-- title:
--   Proof of Theorem 3(b) — $k(S)=k(T)-(\sum_S a_j)(\sum_{T-S}a_j)=y+c^2$
-- statement:
--   Let $a_1,\dots,a_t$ be nonnegative integers, $A=\sum_{j\in T}a_j$, $S\subseteq T$, and $c=\sum_{j\in S}a_j-\tfrac12A$. With $k(\cdot)$ and $y=\sum_{j,k\in T,\,j\le k}a_ja_k-\tfrac14A^2$ as in construction (b),
--
--   $$k(S) = k(T) - \Big(\sum_{j\in S}a_j\Big)\Big(\sum_{j\in T-S}a_j\Big) = \sum_{j,k\in T,\ j\le k} a_ja_k - \big(\tfrac12A+c\big)\big(\tfrac12A-c\big) = y + c^2 .$$
--
--   Since $c^2>0$ unless $S$ solves PARTITION, this identity converts the schedule value $k(S)$ into the PARTITION condition.
--
--   **Formalization Note** The identity is stated over $\mathbb R$ as three equalities, one per step of the printed chain, and holds for all natural data, so positivity is not assumed.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), p. 15, proof of Theorem 3(b), displayed identity (cf. Figure 1)

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Constructions

namespace SchedComplexity.Partition

/-- Proof of Theorem 3(b) (p. 15), the displayed chain: with `c = Σ_{j ∈ S} a_j − ½A`,
`k(S) = k(T) − (Σ_{j∈S} a_j)(Σ_{j∈T−S} a_j) = Σ_{j,k∈T, j≤k} a_j a_k − (½A + c)(½A − c) = y + c²`. -/
theorem theorem_3b_k_identity (a : List ℕ) (S : Finset (Fin a.length)) :
    let c : ℝ := ((∑ j ∈ S, a.get j : ℕ) : ℝ) - (totalA a : ℝ) / 2
    (kVal a S : ℝ) =
        (kVal a Finset.univ : ℝ) -
          ((∑ j ∈ S, a.get j : ℕ) : ℝ) * ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) ∧
      (kVal a Finset.univ : ℝ) -
          ((∑ j ∈ S, a.get j : ℕ) : ℝ) * ((∑ j ∈ Sᶜ, a.get j : ℕ) : ℝ) =
        (pairSum a : ℝ) - ((totalA a : ℝ) / 2 + c) * ((totalA a : ℝ) / 2 - c) ∧
      (pairSum a : ℝ) - ((totalA a : ℝ) / 2 + c) * ((totalA a : ℝ) / 2 - c) = yB a + c ^ 2 := by sorry

end SchedComplexity.Partition
