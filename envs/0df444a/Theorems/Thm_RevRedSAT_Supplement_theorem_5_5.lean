-- Prove2me | Theorems.Thm_RevRedSAT_Supplement_theorem_5_5
-- name    : RevRedSAT.Supplement.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:59:26.658179+00:00
-- url     : https://prove2.me/theorems/c6c3f08e-d31e-4c05-a64d-0310acf41287
-- title:
--   Theorem 5.5 — an effective $2^{o(k)}$ Connected Vertex Cover algorithm gives FPT $=$ W[1]
-- statement:
--   Suppose a deterministic algorithm decides Connected Vertex Cover, parameterized by the budget $k$, within
--
--   $$\Bigl\lfloor 2^{g(k)}\,|w|^{C}\Bigr\rfloor$$
--
--   steps on every code $w$ of an instance $(G,k)$, where $C$ is a constant and $g$ is effectively sublinear: there is a computable $b$ with $g(k)\le k/a$ whenever $a\ge1$ and $k\ge b(a)$. Then FPT $=$ W[1], i.e. Clique is fixed-parameter tractable.
--
--   So under FPT $\neq$ W[1], connectivity prevents the subexponential dependence on the solution size that Vertex Cover has under the SAT assumptions.
--
--   Differences from the source:
--   - encoding: an algorithm whose running time counts bit operations (no machine model named) → a Mathlib TM2 machine with finite stack alphabets, time = number of steps; reason: polynomial changes of model are absorbed by the polynomial factor and the 2^{O(·)} classes
--   - encoding: the explicit binary encoding of the input → fixed self-delimiting codes; every listing order of the input is an admissible code; reason: the codes are injective and of polynomial length; quantifying over all codes adds no precomputed information
--   - generalization: Connected Vertex Cover has a deterministic algorithm (App. C.3: find a vertex cover …) → the premise is a decision algorithm (DecideWithin); reason: a search algorithm yields a decision algorithm within twice its bound, and 2·2^{g} = 2^{g+1} with g + 1 again effectively sublinear (threshold max{b(2a), 2a}); the source's theorem is the special case
--   - encoding: 2^{g(k)}|I|^C with C an absolute (real) constant → ⌊2^{g(k)}·|w|^C⌋ with C ∈ ℕ; reason: ⌈C⌉ gives the same class since |w| ≥ 1
--   - reading: FPT = W[1] → CliqueFPT: Clique is decided within f(ℓ)·|w|^c steps, f computable; reason: W[1] is the closure of Clique under FPT reductions; the proof concludes by an FPT algorithm for Clique
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 5.5, p.37 (printed) = PDF p.39; proof pp.37–38

import Mathlib
import Definitions.Def_RevRedSAT_FiniteAlphabets
import Definitions.Def_RevRedSAT_VCInstance
import Definitions.Def_RevRedSAT_Supplement_DecideWithin
import Definitions.Def_RevRedSAT_Supplement_CVCValid
import Definitions.Def_RevRedSAT_Supplement_CliqueFPT

set_option autoImplicit false

namespace RevRedSAT.Supplement

/-- **Theorem 5.5 (a parameterized barrier for Connected Vertex Cover).**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), Theorem 5.5, p.37: "If Connected Vertex Cover, parameterized by the allowed number k of selected
vertices, has a deterministic algorithm running in time 2^{g(k)}|I|^C, where C is an absolute
constant and g(k) = o(k) effectively, then FPT = W[1]. Here effectiveness means that there is a
computable function b: N≥1 → N such that g(k) ≤ k/a whenever k ≥ b(a)."

If a machine with finite alphabets decides Connected Vertex Cover (instances `(n, G, k)`, codes
`RevRedSAT.IsVCCode`) within `⌊2^{g(k)} · |w|^C⌋` steps for a natural number `C` and an effectively
sublinear `g`, then Clique is fixed-parameter tractable (`CliqueFPT`, the reading of FPT = W[1]).

**Formalization Note** The premise is a decision algorithm; a search algorithm gives one. A real
exponent `C` is replaced by `⌈C⌉` (`|w| ≥ 1`). -/
theorem theorem_5_5 :
    (∃ M : Turing.TM2ComputableAux Bool Bool, FiniteAlphabets M ∧
      ∃ g : ℕ → ℝ, EffectivelySublinear g ∧ ∃ C : ℕ,
        DecideWithin M IsVCCode (fun I => ∃ S, CVCValid I S)
          (fun I w => ⌊(2 : ℝ) ^ g I.k * (w.length : ℝ) ^ C⌋₊)) →
      CliqueFPT := by sorry

end RevRedSAT.Supplement
