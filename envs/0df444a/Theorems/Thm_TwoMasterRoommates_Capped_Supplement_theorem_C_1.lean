-- Prove2me | Theorems.Thm_TwoMasterRoommates_Capped_Supplement_theorem_C_1
-- name    : TwoMasterRoommates.Capped.Supplement.theorem_C_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:35:32.49791+00:00
-- url     : https://prove2.me/theorems/caa77211-151d-40c0-9bbf-819beb246a47
-- title:
--   Theorem C.1 (= Theorem 1.4) — maximum-weight weakly stable perfect matching with one weak master and s outliers
-- statement:
--   Let $V=F\cup S$ be an even population of $N$ agents with complete weak preference lists, $s=|S|$, a supplied weak order $\rho$ on all of $V$ by which every follower ranks its possible partners, and arbitrary rows for the outliers. Let $w$ assign an arbitrary rational weight to every unordered pair. There are a deterministic one-tape Turing machine and absolute constants $C,c,d$, fixed before the instance, such that on the binary code of every such instance, of length $L$, the machine halts within
--
--   $$C\,(s+1)^{c\,s}\,(L+1)^{d}$$
--
--   steps and outputs either a correct report that no weakly stable perfect matching exists, or a weakly stable perfect matching of maximum total weight. Stability and optimality refer to the original weak rows; neither the master tiers nor the outlier ties have a size bound.
--
--   This is the parameterized tractability result of the paper: few arbitrary rows on top of one weak master keep weighted optimization tractable, in contrast to Theorems D.1 and D.6.
--
--   Differences from the source:
--   - encoding: time 2^{O(s log(s+1))} poly(N, L) → C·(s+1)^{c·s}·(L+1)^d steps with absolute C, c, d chosen before N and the instance; reason: 2^{c s log₂(s+1)} = (s+1)^{c s} and N ≤ L, so the two classes of bounds coincide
--   - encoding: an unspecified machine model and input representation → a deterministic one-tape Turing machine of the published Cook framework reading the binary code (N, outlier flags, ρ, outlier rows, weights as reduced fractions); reason: polynomial simulation overhead and a polynomial change of representation are absorbed by the bound
--   - encoding: the algorithm does not refine a preference tie → correctness of both output branches is judged against the original weak rows; reason: refining a tie would change the weakly stable family, so exact correctness on the weak rows carries the claim
--   - encoding: a maximum-weight weakly stable perfect matching, or a report of nonexistence → the output `true` followed by the code of the matching, or `[false]`; reason: a fixed tagged output code
--   - encoding: complete weak orders (the master ρ and the outlier rows) → integer rank functions, smaller is better, equal values tied; reason: every weak order on a finite set is represented by integer ranks and only comparisons are used (§3)
-- source:
--   Bin Yu, STOC 2027 submission #225 (October 2026), p. 18 (PDF p. 19), Theorem C.1 (= Theorem 1.4, p. 2, PDF p. 3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_TwoMasterRoommates_Capped_Supplement_OneMaster

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TwoMasterRoommates.Capped.Supplement

/-- Theorem C.1 (= Theorem 1.4), Bin Yu, STOC 2027 submission #225, p. 18 (PDF 19): one
deterministic Turing machine, on every even one-master-plus-`s`-outliers instance with arbitrary
rational edge weights, outputs a maximum-weight weakly stable perfect matching or correctly
reports that none exists, within `C · (s+1)^(c·s) · (L+1)^d` steps, `L` the binary input length,
with absolute constants `C, c, d` fixed before the instance. -/
theorem theorem_C_1 :
    ∃ (Γ : Type) (_ : Fintype Γ) (ι₁ ι₂ : Bool ↪ Γ) (T : CookPvsNP.TM Γ) (C c d : ℕ),
      ∀ (N : ℕ) (I : OneMasterInstance N) (w : Sym2 (Fin N) → ℚ), Even N →
        T.HaltsWithin (C * (I.s + 1) ^ (c * I.s) * ((I.enc w).length + 1) ^ d)
            ((I.enc w).map ι₁) ∧
        ∃ y : List Bool, I.CorrectC1 w y ∧
          T.output (T.run (C * (I.s + 1) ^ (c * I.s) * ((I.enc w).length + 1) ^ d)
            (T.init ((I.enc w).map ι₁))) = y.map (some ∘ ι₂) := by sorry

end TwoMasterRoommates.Capped.Supplement
