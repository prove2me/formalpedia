-- Prove2me | Theorems.Thm_RevRedSAT_lemma_4_7
-- name    : RevRedSAT.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:46:52.885841+00:00
-- url     : https://prove2.me/theorems/06843d23-6ebd-4973-948c-276c1c9f70d6
-- title:
--   Lemma 4.7 — bounded fan-in circuits become 3-CNF with unique extensions
-- statement:
--   Fix an integer $d\ge1$. There are a polynomial-time algorithm and a constant $K$ (depending on $d$) such that, given a Boolean circuit $C$ with $p$ input bits, $g$ gates and one output bit, every gate having at most $d$ inputs, the algorithm constructs a CNF formula $\varphi$ of width at most $3$ over $n$ variables, the first $p$ of which are the input bits, with
--
--   $$n\le p+K(g+1)\qquad\text{and}\qquad\#\text{clauses}\le K(g+1),$$
--
--   such that for every input assignment $x\in\{0,1\}^p$:
--
--   1. if $C(x)=1$, exactly one assignment of all $n$ variables extending $x$ satisfies $\varphi$;
--   2. if $C(x)=0$, no assignment extending $x$ satisfies $\varphi$.
--
--   This is the Tseitin-style conversion used to express counters and other tests in 3-CNF without changing the number of satisfying assignments.
--
--   **Formalization Note** The input bits are the variables $0,\dots,p-1$ of the formula, and clauses are counted with multiplicity.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{o(·)}, 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - encoding: in polynomial time → a finite-alphabet machine and constants C, e chosen before the input, time ≤ C·(input size + 1)^e; reason: the standard meaning, with the constants fixed before the input
--   - encoding: the formula's variables include the p input variables → the input bits are the formula variables 0, …, p − 1; reason: a naming convention; any renaming of variables gives the same formula
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 4.7, p.33 (printed) = PDF p.35

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_encCNF
import Definitions.Def_RevRedSAT_Circuit

set_option autoImplicit false

namespace RevRedSAT

/-- **Lemma 4.7 (circuits to 3-CNF with unique extensions).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Lemma 4.7, p.33: "Fix a positive integer d. Let C be a Boolean circuit with p input bits, g
gates, and one output bit, where each gate has at most d inputs. In polynomial time, one can
construct a 3-CNF formula with p + O(g + 1) variables and O(g + 1) clauses such that each input
assignment has exactly one satisfying extension if C outputs one, and no satisfying extension if C
outputs zero. The constants in these bounds may depend on d."

For every `d ≥ 1` there are a finite-alphabet machine `M` and constants `K, C, e` such that on the
code of every circuit of fan-in at most `d` with `p` inputs and `g` gates, `M` outputs within
`C·(|code| + 1)^e` steps the code of a formula `φ` over `n ≥ p` variables, of width at most `3`, with
`n ≤ p + K(g + 1)` and at most `K(g + 1)` clauses, whose first `p` variables are the circuit inputs:
every input assignment `x` with output `1` has exactly one extension to all `n` variables satisfying
`φ`, and every `x` with output `0` has none.

**Formalization Note** The input variables are the variables `0, …, p − 1` of the formula
(`Fin.castLE`); clauses are counted with multiplicity (list length), which is at least the number
of distinct clauses. -/
theorem lemma_4_7 :
    ∀ d : ℕ, 1 ≤ d →
      ∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧ ∃ K C e : ℕ,
        ∀ Ckt : Circuit, Ckt.WellFormed d →
          ∃ (n : ℕ) (φ : MainResults.CNF n) (h : Ckt.p ≤ n),
            HMBinPacking.OutputsWithin M (encCircuit Ckt) (encCNF φ)
              (C * ((encCircuit Ckt).length + 1) ^ e) ∧
            width φ ≤ 3 ∧ n ≤ Ckt.p + K * (Ckt.gates.length + 1) ∧
            φ.length ≤ K * (Ckt.gates.length + 1) ∧
            ∀ x : Fin Ckt.p → Bool,
              (Ckt.eval x = true →
                ∃! a : Fin n → Bool, (∀ i, a (Fin.castLE h i) = x i) ∧ SatBy a φ) ∧
              (Ckt.eval x = false →
                ∀ a : Fin n → Bool, (∀ i, a (Fin.castLE h i) = x i) → ¬ SatBy a φ) := by sorry

end RevRedSAT
