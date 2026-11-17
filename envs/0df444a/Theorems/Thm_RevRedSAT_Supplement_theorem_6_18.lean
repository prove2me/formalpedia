-- Prove2me | Theorems.Thm_RevRedSAT_Supplement_theorem_6_18
-- name    : RevRedSAT.Supplement.theorem_6_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:01:57.156188+00:00
-- url     : https://prove2.me/theorems/1b8396ae-e4ef-43de-8f1a-51d36b45cec5
-- title:
--   Theorem 6.18 — an effective $2^{o(k)}$ Min-Weight 3-SAT algorithm gives FPT $=$ W[1]
-- statement:
--   Suppose a deterministic algorithm decides Min-Weight 3-SAT (a CNF formula of width at most $3$ and a budget $k$: is there a satisfying assignment with at most $k$ ones?) within
--
--   $$\Bigl\lfloor 2^{g(k)}\,|w|^{C}\Bigr\rfloor$$
--
--   steps on every code $w$, where $C$ is a constant and $g$ is effectively sublinear: given $a\ge1$ one can compute $b(a)$ with $g(t)\le t/a$ for all $t\ge b(a)$. Then FPT $=$ W[1], i.e. Clique is fixed-parameter tractable.
--
--   Min-Weight $d$-SAT generalizes $d$-Hitting Set by allowing negative literals; the theorem shows that the subexponential algorithms for $d$-Hitting Set do not extend to it unless FPT $=$ W[1].
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - generalization: Min-Weight 3-SAT has a deterministic 2^{o(k)}|I|^{O(1)}-time algorithm (App. C.5: find a satisfying assignment …) → the premise is a decision algorithm (DecideWithin); reason: a search algorithm yields a decision algorithm within twice its bound, and g + 1 is again effectively sublinear; the source's theorem is the special case
--   - encoding: 2^{g(k)}|I|^C with C an absolute (real) constant → ⌊2^{g(k)}·|w|^C⌋ with C ∈ ℕ; reason: ⌈C⌉ gives the same class since |w| ≥ 1
--   - reading: FPT = W[1] → CliqueFPT: Clique is decided within f(ℓ)·|w|^c steps, f computable; reason: W[1] is the closure of Clique under FPT reductions; the proof concludes by an FPT algorithm for Clique
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.18, p.49 (printed) = PDF p.51; App. C.5, p.94

import Mathlib
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_encCNF
import Definitions.Def_RevRedSAT_Supplement_DecideWithin
import Definitions.Def_RevRedSAT_Supplement_SATInstance
import Definitions.Def_RevRedSAT_Supplement_CliqueFPT

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **Theorem 6.18 (a boundary for Min-Weight 3-SAT).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 6.18, p.49: "If Min-Weight 3-SAT, parameterized by the allowed number k of ones, has a
deterministic 2^{o(k)}|I|^{O(1)}-time algorithm with an effective subexponential bound, then
FPT = W[1]. Here effectiveness means that the running time is bounded by 2^{g(k)}|I|^C for a
constant C and a function g such that, given any positive integer a, one can compute a threshold
b(a) satisfying g(t) ≤ t/a for all t ≥ b(a)."

If a machine with finite alphabets decides Min-Weight 3-SAT (a CNF formula of width at most `3` and
a budget `k`, coded as `encCNF φ ++ encNat k`; YES when some satisfying assignment sets at most `k`
variables to one) within `⌊2^{g(k)} · |w|^C⌋` steps for a natural number `C` and an effectively
sublinear `g`, then Clique is fixed-parameter tractable (`CliqueFPT`, the reading of FPT = W[1]).

**Formalization Note** Width counts distinct literals of a clause (App. C.5). A real `C` is replaced
by `⌈C⌉`. -/
theorem theorem_6_18 :
    (∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
      ∃ g : ℕ → ℝ, EffectivelySublinear g ∧ ∃ C : ℕ,
        DecideWithin M (fun I w => width I.φ ≤ 3 ∧ IsSATCode I w) MinWeightYes
          (fun I w => ⌊(2 : ℝ) ^ g I.k * (w.length : ℝ) ^ C⌋₊)) →
      CliqueFPT := by sorry

end RevRedSAT.Supplement
