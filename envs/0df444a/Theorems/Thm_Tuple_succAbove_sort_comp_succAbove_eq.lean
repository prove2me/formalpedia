-- Prove2me | Theorems.Thm_Tuple_succAbove_sort_comp_succAbove_eq
-- name    : Tuple.succAbove_sort_comp_succAbove_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/fe6bdd97-ac52-55d8-8c59-1085da00621e
-- title:
--   Sorting commutes with deleting one entry
-- statement:
--   Fix a natural number $n$ and a linearly ordered type $\iota$. Let $u \colon \mathrm{Fin}(n+1) \to \iota$ be a tuple which is injective as a function, let $i \in \mathrm{Fin}(n+1)$ be an index and let $k \in \mathrm{Fin}(n)$. Write $\sigma =$ `Tuple.sort u` for the sorting permutation of $u$, i.e. the permutation of $\mathrm{Fin}(n+1)$ such that $u \circ \sigma$ is monotone (ties being broken by position), and write $\delta_i =$ `Fin.succAbove i` for the order embedding $\mathrm{Fin}(n) \to \mathrm{Fin}(n+1)$ whose image omits $i$. The assertion is the pointwise identity
--   $$\delta_i\bigl(\operatorname{sort}(u \circ \delta_i)(k)\bigr) = \sigma\bigl(\delta_{\sigma^{-1}(i)}(k)\bigr),$$
--   where $\operatorname{sort}(u \circ \delta_i)$ is the sorting permutation of the $n$-tuple obtained from $u$ by deleting the entry at position $i$, and $\sigma^{-1}(i)$ is the rank of $u(i)$ in the sorted order. Thus the embedding of the sorted face into $\mathrm{Fin}(n+1)$ agrees with $\sigma$ composed with the face omitting the rank of $i$; equivalently, $(u \circ \delta_i) \circ \operatorname{sort}(u \circ \delta_i) = (u \circ \sigma) \circ \delta_{\sigma^{-1}(i)}$.
--
--   A combinatorial compatibility between sorting a tuple and deleting one of its entries: deleting the $i$-th entry and sorting gives the same ordered tuple as sorting and then deleting the entry of rank $\sigma^{-1}(i)$. It is used in the construction of ordered affine covers and the associated Čech-style differentials on presheaves of modules, where faces of an index tuple must be reindexed by their sorted representatives.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Tuple_succAbove_sort_comp_succAbove_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Tuple.succAbove_sort_comp_succAbove_eq
    {n : ℕ} {ι : Type*} [LinearOrder ι] (u : Fin (n + 1) → ι) (hu : Function.Injective u) (i : Fin (n + 1)) (k : Fin n) :
    i.succAbove (Tuple.sort (u ∘ i.succAbove) k) = Tuple.sort u (((Tuple.sort u).symm i).succAbove k) := by sorry
