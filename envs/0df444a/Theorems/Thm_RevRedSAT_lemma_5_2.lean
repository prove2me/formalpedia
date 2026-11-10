-- Prove2me | Theorems.Thm_RevRedSAT_lemma_5_2
-- name    : RevRedSAT.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:48:31.914132+00:00
-- url     : https://prove2.me/theorems/c0fd2c93-895f-41c0-b84e-9b86baf010e2
-- title:
--   Lemma 5.2 — Vertex Cover of the kernel as a 3-CNF formula with O(s) variables
-- statement:
--   Let $G'$ be a graph on $s$ vertices and $k'$ an integer with $0\le k'<s$. In polynomial time one can construct a CNF formula $\varphi$ of width at most $3$ with $O(s)$ variables and $O(s+|E(G')|)$ clauses, with one selection variable $x_v$ for each vertex $v$, such that the satisfying assignments of $\varphi$ correspond one-to-one to the vertex covers of $G'$ of size at most $k'$, the cover of an assignment being $\{v: x_v=1\}$:
--
--   1. every satisfying assignment selects a vertex cover of size at most $k'$;
--   2. every vertex cover of size at most $k'$ is selected by exactly one satisfying assignment.
--
--   **Formalization Note** $G'$ is given as an instance on its own vertex set $\{0,\dots,s-1\}$, $x_v$ is the formula variable $v$, and the constants in the $O(\cdot)$ bounds are absolute.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: in polynomial time → a finite-alphabet machine and constants C, e chosen before the input, time ≤ C·(input size + 1)^e; reason: the standard meaning, with the constants fixed before the input
--   - encoding: one selection variable x_v for each v ∈ V(G′) → x_v is the formula variable v; reason: a naming convention
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 5.2, p.35 (printed) = PDF p.37 (context: s = |V(G′)|, 0 ≤ k′ < s ≤ 2k)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_encCNF
import Definitions.Def_RevRedSAT_VCInstance

set_option autoImplicit false

namespace RevRedSAT

/-- **Lemma 5.2 (Vertex Cover as a 3-CNF formula with O(s) variables).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 5.2, p.35: "In polynomial time, one can construct a 3-CNF formula F with O(s) variables
and O(s + |E(G′)|) clauses whose satisfying assignments correspond one-to-one to the vertex covers of
G′ of size at most k′. There is one selection variable x_v for each v ∈ V(G′); the corresponding
cover is {v : x_v = 1}." Context (p.35): s = |V(G′)| and "0 ≤ k′ < s ≤ 2k".

There are a finite-alphabet machine and absolute constants `K, C, e` such that on every code `w` of
a Vertex Cover instance `(G', k')` on `s` vertices with `k' < s`, the machine outputs within
`C·(|w| + 1)^e` steps the code of a formula `φ` of width at most `3` over `N` variables,
`s ≤ N ≤ K·s`, with at most `K·(s + |E(G')|)` clauses, such that, with `x_v` the variable `v`:
every satisfying assignment selects a vertex cover `{v : x_v = 1}` of size at most `k'`, and every
vertex cover of size at most `k'` is selected by exactly one satisfying assignment.

**Formalization Note** `G'` is given as an instance on its own vertex set `{0, …, s − 1}`; the
budget `s ≤ 2k` of the context relates `s` to the original budget only and plays no role here. -/
theorem lemma_5_2 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ K C e : ℕ,
      ∀ (I : VCInstance) (w : List Bool), IsVCCode I w → I.k < I.n →
        ∃ (N : ℕ) (φ : MainResults.CNF N) (h : I.n ≤ N),
          HMBinPacking.OutputsWithin M w (encCNF φ) (C * (w.length + 1) ^ e) ∧
          width φ ≤ 3 ∧ N ≤ K * I.n ∧ φ.length ≤ K * (I.n + I.G.edgeSet.ncard) ∧
          (∀ a : Fin N → Bool, SatBy a φ →
            VCValid I (Finset.univ.filter fun v => a (Fin.castLE h v) = true)) ∧
          ∀ S : Finset (Fin I.n), VCValid I S →
            ∃! a : Fin N → Bool, SatBy a φ ∧
              (Finset.univ.filter fun v => a (Fin.castLE h v) = true) = S := by sorry

end RevRedSAT
