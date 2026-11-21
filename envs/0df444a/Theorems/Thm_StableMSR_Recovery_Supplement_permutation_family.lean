-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_permutation_family
-- name    : StableMSR.Recovery.Supplement.permutation_family
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T03:18:54.884648+00:00
-- url     : https://prove2.me/theorems/f4026d15-8a83-4a0f-b92c-023ddb7bbdad
-- title:
--   Theorem B.2 — polynomial permutation family enumeration
-- statement:
--   For every nonempty finite ordered set $V$, write $m=|V|$. One deterministic finite program receiving only $m$ enumerates a nonempty multiset $\mathcal F_V$ of permutations. For some absolute positive integers $a,b$, its halting steps, charged work, and family length are at most $a m^b$, simultaneously for every $m\ge1$. For every nonempty $T\subseteq V$ and $z\in T$,
--
--   $$\Pr_{\pi\in\mathcal F_V}[z\text{ precedes every }y\in T\setminus\{z\}]\le\frac3{2|T|}.$$
--
--   The probability counts list occurrences, including repeated permutations. The order identifies $V$ with $0,\ldots,m-1$; every finite ordered set is represented. Both enumeration time and family size are polynomial, unlike a bound for a family supplied by an external prime parameter. This is the derandomization companion used in the goal's proof.
--
--   Differences from the source:
--   - encoding: Every finite nonempty ordered V, a multiset of polynomially many permutations with polynomial enumeration time → Order-preserving identification with Fin m, a deterministic input-m interpreter execution and outputSets decoded as a nonempty list of permutation lists; reason: No finite ordered instance is excluded; repeated lists count separately and the output list itself must be produced within charged polynomial work
--   - encoding: |V|^O(1) for time and family size → One pair of absolute positive natural constants a,b bounds steps, work and list length by a*m^b for every m >= 1; reason: The proof uses fixed absolute hash parameters and polynomial prime search; there is no source numerical end-to-end exponent to invent
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Theorem B.2, p. 23; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Supplement_RandomExecution

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

theorem permutation_family :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      ∃ P : MinSumFPT.Program, DeterministicProgram P ∧
        ∀ m : ℕ, 1 ≤ m → ∃ t ≤ a * m ^ b,
          let s := execute P m 0 (fun _ _ => 0) t
          s.halted = true ∧ s.work ≤ a * m ^ b ∧
          PermutationFamily m (MinSumFPT.outputSets s) ∧
          (MinSumFPT.outputSets s).length ≤ a * m ^ b ∧
          ∀ T : Finset ℕ, T ⊆ Finset.range m → T.Nonempty →
            ∀ z ∈ T, firstFraction (MinSumFPT.outputSets s) T z ≤ 3 / (2 * (T.card : ℝ)) := by sorry

end StableMSR.Recovery.Supplement
