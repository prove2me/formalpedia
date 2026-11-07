-- Prove2me | Theorems.Thm_ShallowSym_eq_6_pair_circuit
-- name    : ShallowSym.eq_6_pair_circuit
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:01:09.607503+00:00
-- url     : https://prove2.me/theorems/074f6f5c-1c7b-4151-8504-789c8d58680b
-- title:
--   Eq. (6): the pair function is a $\Pi_{d-1}$ formula of the inductive size
-- statement:
--   Let $m\ge 2$ and let $S:\mathbb N\to\mathbb N$ be such that every symmetric function on $r$ variables, for every $r$, is computed by a $\Pi_m$ formula with at most $S(r)$ gates (the inductive hypothesis, with $m=d-1$). Let $\beta$ partition the $n$ coordinates into $k$ blocks $B_0,\dots,B_{k-1}$, let $s$ be shifts in $\mathbb Z/k\mathbb Z$, and let $i\ne j$ be two blocks. Then the pair function
--
--   $$x\mapsto 1\big[w_i(x)+s_i\not\equiv w_j(x)+s_j\pmod k\big]$$
--
--   on all $n$ variables is computed by a $\Pi_m$ formula with at most
--
--   $$S\big(|B_i|+|B_j|\big)$$
--
--   gates.
--
--   The pair function depends only on $w_i-w_j$, hence is a symmetric function of block $i$'s variables and the negations of block $j$'s variables; this is what lets the induction on the depth go through. With $|B_i|,|B_j|\le\lceil n/k\rceil$ and the inductive size bound $2^{O(r^{1/(d-2)})}$ it gives the size $2^{O((n/k)^{1/(d-2)})}$ of eq. (6).
--
--   **Formalization Note** Formulas are strictly layered alternating AND/OR trees over literals (`ShallowSym.Layer`): every literal sits at depth exactly $d$, a gate at level $\ell$ reads only nodes of level $\ell-1$, gates of arbitrary (also empty) fan-in, size = number of gates.
--
--   Differences from the source:
--   - reading: 'the inductive hypothesis tells us … a Πd−1 circuit of size 2^{O((n/k)^{1/(d−2)})}' → for any size function S that the inductive hypothesis provides for all symmetric functions, a Π_m formula of size ≤ S(|Bᵢ| + |Bⱼ|); reason: the O-bound in (6) is the inductive size bound evaluated at the 2⌈n/k⌉ variables of the two blocks; the explicit transfer gives (6) for the induction's size function and is the exact step the induction uses
--   - generalization: blocks of length at most ⌈n/k⌉ → an arbitrary partition β : Fin n → Fin k; reason: the length bound only enters the O-form of the size; specializes to the paper's partitions
--   - encoding: depth d − 1 with d ≥ 3 → any level m ≥ 2; reason: m = d − 1 ranges over exactly the levels m ≥ 2; same instances
--   - encoding: pairs 1 ≤ i < j ≤ k → blocks i ≠ j in Fin k; reason: the pair function is symmetric in i and j; same functions
--   - reading: circuits → formulas (ShallowSym.Layer), in the hypothesis and the conclusion; reason: the mission's circuit model is the formula model of Theorem 1, whose induction hypothesis is about formulas
-- source:
--   Lecomte, Ramakrishnan, Optimal Shallow Circuits for Majority, arXiv:2609.34029 (version of 2026-11-01, sha256 6f46ce49…), §4 'Anatomy of a test', eq. (6), p.11

import Mathlib
import Definitions.Def_ShallowSym_IsSymmetric
import Definitions.Def_ShallowSym_Layer
import Definitions.Def_ShallowSym_pairFn

namespace ShallowSym

/-- §4 "Anatomy of a test", eq. (6), p.11. V. Lecomte, P. Ramakrishnan, *Optimal Shallow Circuits for Majority*, arXiv:2609.34029
(version of 2026-11-01, sha256 6f46ce49…).

"The key observation is that the constituent functions 1[wi + si ≢ wj + sj (mod k)] depend on at
most 2⌈n/k⌉ variables, and are nearly symmetric functions over these variables. Since these
functions only depend on the difference wi − wj, they are symmetric if we treat their input as
block i’s variables and the negations of block j’s variables. Thus, the inductive hypothesis tells
us that 1[wi + si ≢ wj + sj (mod k)] can be expressed as a Πd−1 circuit of size
2^{O((n/k)^{1/(d−2)})}. (6)"

Let `m ≥ 2` and `S : ℕ → ℕ` be a size bound such that every symmetric function on `r`
variables (for every `r`) has a Π_m formula with at most `S r` gates (the inductive hypothesis,
`m = d − 1`). Then for every partition `β : Fin n → Fin k`, shifts `s` and blocks `i ≠ j`, the
pair function `1[w_i + s_i ≢ w_j + s_j (mod k)]` on all `n` variables has a Π_m formula with at
most `S(|B_i| + |B_j|)` gates, where `B_i = β⁻¹(i)`.

**Formalization Note.** The O-bound of (6) is stated as an explicit transfer of the inductive
hypothesis' size function to the actual block sizes; with `|B_i|, |B_j| ≤ ⌈n/k⌉` and the size
function of the induction, this gives (6). Blocks are arbitrary (not necessarily contiguous or of
equal size). The level is `m = d − 1 ≥ 2` (the induction step has `d ≥ 3`); at `m = 1`
the hypothesis would be unsatisfiable (Parity on two variables has no Π₁ formula). -/
theorem eq_6_pair_circuit (m : ℕ) (hm : 2 ≤ m) (S : ℕ → ℕ)
    (hS : ∀ (r : ℕ) (g : Cube r → Bool), IsSymmetric g →
      ∃ ψ : Layer r m, (∀ y, evalPi m ψ y = g y) ∧ size m ψ ≤ S r)
    {n k : ℕ} (β : Fin n → Fin k) (s : Fin k → ZMod k) (i j : Fin k) (hij : i ≠ j) :
    ∃ ψ : Layer n m, (∀ x, evalPi m ψ x = pairFn β s i j x) ∧
      size m ψ ≤ S ((Finset.univ.filter (fun a => β a = i)).card +
        (Finset.univ.filter (fun a => β a = j)).card) := by sorry

end ShallowSym
