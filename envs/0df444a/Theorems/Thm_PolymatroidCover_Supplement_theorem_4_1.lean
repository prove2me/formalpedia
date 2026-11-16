-- Prove2me | Theorems.Thm_PolymatroidCover_Supplement_theorem_4_1
-- name    : PolymatroidCover.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:52:16.25938+00:00
-- url     : https://prove2.me/theorems/4ced88e6-eaa0-4600-b332-a0fe1ad9e12d
-- title:
--   Theorem 4.1 — push-relabel keeps $P - C \le n$ and performs at most $n^2$ pushes and $n^2$ relabels
-- statement:
--   Let $f$ be a $d$-polymatroid on $E$ with $n := |E|$ and $f(E) > 0$, and run Algorithm 2 (push-relabel) with any number of colors
--
--   $$
--   k \ge (4d-2)\cdot\chi^\circ(f).
--   $$
--
--   Let $P := p(E)$ be the total level of all elements and $C := \sum_{j=1}^k p(S_j)$ the total level of the colored elements, where $p(X) := \sum_{e\in X} p(e)$. Then, at every moment of every execution of the algorithm (for every choice of the uncolored element to insert and every tie-breaking in the orderings),
--
--   1. $P - C \le n$;
--   2. the number of pushes performed so far is at most $n^2$;
--   3. the number of relabels performed so far is at most $n^2$.
--
--   In particular every execution terminates after at most $2n^2$ iterations of the while-loop, which is what makes the covering algorithm of Theorem 1.2 polynomial.
--
--   **Formalization Note** The states of the algorithm are recorded at the head of the while-loop, and "at every moment of every execution" means every state reachable from the initial state by the step relation `PushRelabelStep`. The inequality $P - C \le n$ is stated as $P \le C + n$.
--
--   Differences from the source:
--   - encoding: ground set E, f : 2^E → Z≥0 → E = Fin n, f : Finset (Fin n) → ℕ; reason: the mission's published convention; same instances
--   - encoding: f with f(E) > 0 implicit (χ°(f) in eq. (1) is defined only then) → hypothesis 0 < f univ; reason: it excludes exactly the instances for which the maximum in eq. (1) is over the empty set
--   - generalization: standing assumption of §2 (p.9): f(e) > 0 for every e ∈ E → no self-loop hypothesis; reason: a self-loop is never blocked (adding it keeps a set independent) and is pushed with an empty blocking set at its first attempt; deleting self-loops does not change χ°(f) (p.9), so the run on f projects onto a run on the loopless restriction and the bounds for n' ≤ n elements imply those for n; on loopless f the statement is the source's
--   - encoding: the algorithm (Algorithm 2) with arbitrary tie-breaking and choice of the uncolored element → every state reachable from prInit n k by the relation PushRelabelStep, which allows every such choice; reason: "the algorithm maintains" and "performs at most" are claims about every execution; the counters in the state count the pushes and relabels performed so far
--   - encoding: P − C ≤ n → P ≤ C + n in ℕ; reason: avoids truncated subtraction; equivalent
-- source:
--   Bérczi, Chandrasekaran, Chekuri, Liu, Ravi, Approximate Covering and Packing in Polymatroids, STOC 2027 submission (manuscript sha256 47f38a6f…), §4, Theorem 4.1, p.22 (PDF p.24); P, C, n defined p.21 (PDF p.23)

import Mathlib
import Definitions.Def_PolymatroidCover_IsDPolymatroid
import Definitions.Def_PolymatroidCover_chiCirc
import Definitions.Def_PolymatroidCover_Supplement_PushRelabelStep

namespace PolymatroidCover.Supplement

open PolymatroidCover

/-- Theorem 4.1 (Bérczi–Chandrasekaran–Chekuri–Liu–Ravi, *Approximate Covering and Packing in Polymatroids*, STOC 2027 submission (manuscript sha256 47f38a6f…), §4, printed p.22 = PDF p.24): "The algorithm maintains the invariant that
`P − C ≤ n`. Moreover, the algorithm performs at most `n²` pushes and at most `n²` relabels."
Here (printed p.21 = PDF p.23) `n := |E|`, `P := p(E)` is the total level of all elements and
`C := ∑_{j=1}^k p(S_j)` the total level of the colored elements, for Algorithm 2 run on a
`d`-polymatroid `f` with `k ≥ (4d − 2)·χ°(f)` colors.

For every `d`-polymatroid `f` on `E = Fin n` with `f(E) > 0`, every `k` with
`(4d − 2)·χ°(f) ≤ k`, and every state `σ` reachable from the initial state by iterations of the
while-loop (any choice of the uncolored element and any tie-breaking),
`P ≤ C + n`, the number of pushes performed is at most `n²` and the number of relabels at most
`n²`.

**Formalization Note** `P − C ≤ n` is stated as `P ≤ C + n` (no natural subtraction). Reachable
states are the reflexive–transitive closure of `PushRelabelStep` from `prInit n k`; the counters
in the state count the operations performed so far along the execution. `0 < f univ` is the
hypothesis under which `χ°(f)` of eq. (1) is defined (the maximum in eq. (1) is over a nonempty
set). The standing no-self-loop assumption of §2 is not assumed: a self-loop is never blocked and is
pushed with an empty blocking set at its first attempt. -/
theorem theorem_4_1 {n d k : ℕ} (f : Finset (Fin n) → ℕ) (hf : IsDPolymatroid d f)
    (hE : 0 < f Finset.univ) (hk : (4 * (d : ℤ) - 2) * (chiCirc f : ℤ) ≤ (k : ℤ))
    (σ : PRState n k) (hσ : Relation.ReflTransGen (PushRelabelStep f) (prInit n k) σ) :
    levelSum σ.p Finset.univ ≤ (∑ j : Fin k, levelSum σ.p (σ.S j)) + n ∧
      σ.pushes ≤ n ^ 2 ∧ σ.relabels ≤ n ^ 2 := by sorry

end PolymatroidCover.Supplement
