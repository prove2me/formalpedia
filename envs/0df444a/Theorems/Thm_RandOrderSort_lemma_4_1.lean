-- Prove2me | Theorems.Thm_RandOrderSort_lemma_4_1
-- name    : RandOrderSort.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:06:55.887828+00:00
-- url     : https://prove2.me/theorems/ca7fb666-365b-4ab1-a157-adf582e11ac0
-- title:
--   Lemma 4.1 — accounting for crossings
-- statement:
--   Let $n\ge 16T$. On every execution and for every cut $q$ of the strict key order,
--   $$C(q)\le(T-1)+2F+\sum_{\mathrm{op}}D_{\mathrm{op}}(q),\qquad F\le L+k,$$
--   where the sum runs over all arrival and reallocation operations after the initial block, and $F$ is the number of nonempty fresh allocations after the initial block. The arrival and reallocation charges of the final one-bucket phase together are less than $2060$.
--
--   This reduces the crossing count to the replacement charges of the operations, which the rest of §4 bounds.
--
--   **Formalization Note** The cut is $c\in\{0,\dots,n\}$, between the 0-based ranks $c-1$ and $c$, outer cuts included. A numerical threshold $q$ distinct from every key is the case where $c$ is the number of keys below $q$.
--
--   Differences from the source:
--   - encoding: a cut q distinct from every key → a rank cut c ≤ n of the strict key order (`rankCut`); reason: p.20: "The accounting also covers cuts in the strict key order"; a numerical threshold is the case where c is the number of keys below q
-- source:
--   Kang, Fan, Optimal High Probability Bounds for Random Order Online Sorting, arXiv:2610.15438 (version of 2026-11-01), Lemma 4.1, p.20, display (19)

import Mathlib
import Definitions.Def_RandOrderSort_empiricalSort
import Definitions.Def_RandOrderSort_Dop

namespace RandOrderSort

/-- **Lemma 4.1 (Accounting for crossings)**, Kang, Fan, *Optimal High Probability Bounds for Random Order Online Sorting*, arXiv:2610.15438 (version of 2026-11-01), p.20: "For n ≥ 16T, on every execution,
C(q) ≤ (T − 1) + 2F + ∑_op D_op(q), F ≤ L + k, (19) where the sum runs over all arrival and
reallocation operations after the initial block. The arrival and reallocation charges of the final
one-bucket phase together are less than 2060."

**Formalization Note.** "The accounting also covers cuts in the strict key order" (p.20): the cut
is any cut `c ∈ {0, …, n}` of the strict key order (between 0-based ranks `c − 1` and `c`, outer
cuts included), which is the most general cut distinct from every key; a numerical threshold is the
special case `c = #{keys below q}`. `C(q)` counts adjacent output cells on opposite sides of the
cut; `D_op` is computed from the run's requests; the final phase is phase `L + k − 1`. -/
theorem lemma_4_1 : ∀ n, 16 * T ≤ n → ∀ (x : Fin n → ℝ) (π σ : Equiv.Perm (Fin n)) (c : ℕ), c ≤ n →
    crossings empiricalSort x π σ (fun t => rankCut n (ltOf x π σ) c t.1 = true) ≤
      (T - 1) + 2 * F n + ∑ p ∈ Finset.range (numPhases n),
        (Dop (rankCut n (ltOf x π σ) c) (opReqs (runOf x π σ) p false) +
          Dop (rankCut n (ltOf x π σ) c) (opReqs (runOf x π σ) p true)) ∧
    F n ≤ L n + k n ∧
    Dop (rankCut n (ltOf x π σ) c) (opReqs (runOf x π σ) (numPhases n - 1) false) +
      Dop (rankCut n (ltOf x π σ) c) (opReqs (runOf x π σ) (numPhases n - 1) true) < 2060 := by sorry

end RandOrderSort
