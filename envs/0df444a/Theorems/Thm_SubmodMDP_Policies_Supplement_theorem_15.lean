-- Prove2me | Theorems.Thm_SubmodMDP_Policies_Supplement_theorem_15
-- name    : SubmodMDP.Policies.Supplement.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:32:14.602783+00:00
-- url     : https://prove2.me/theorems/7218f275-572f-458b-8535-fac881847a29
-- title:
--   Theorem 15 — deterministic combinatorial orienteering without a length bound
-- statement:
--   Let $G=(V,A)$ be a finite directed graph with $n=|V|$ and endpoints $s,t$, and assume some $s$-$t$ walk exists. Let $f$ be a nonnegative monotone submodular value oracle, and let $\mathrm{OPT}$ be its maximum reward over all finite $s$-$t$ walks, with no length bound.
--
--   There exist a positive absolute integer $c$ and an integer-indexed family of deterministic combinatorial programs such that for every real $\varepsilon>0$ there is $K_\varepsilon>0$, independent of the instance and oracle, for which the program indexed by $k=\max\{1,\lceil2/\varepsilon\rceil\}$ returns an $s$-$t$ walk $W$ in at most $(n+1)^{ck}$ charged operations and
--
--   $$f(W)\ge\frac{\mathrm{OPT}}{K_\varepsilon n^\varepsilon}.$$
--
--   The program implements the specified polynomial-size general-to-layered reduction, Algorithm 5, and reconstruction along fixed connecting paths. It is deterministic in the published instruction-level sense: no random instruction occurs. No length function, budget, normalized-reward assumption or reward-magnitude bound is part of the input. This companion theorem uses Lemma 14 and is independent of the LP-based MDP goal.
--
--   Differences from the source:
--   - reading: word-RAM operations with input and oracle values fitting a word (footnote 2) → the unchanged published word-charged integer RAM, including its value query and uniform rand M; reason: reuse the accepted base machine model; word length covers input integers and all oracle numerators and denominators, and every RAM run must halt within the bound
--   - reading: nonnegative real-valued oracle rewards → nonnegative rational-valued oracle rewards, using the accepted base finite-representation convention; reason: footnote 2 requires finite word representations; no normalization, integral-reward hypothesis or magnitude bound is added
--   - encoding: arbitrary finite directed s-t walks and their optimum → Mathlib Digraph on Fin n and the maximum over achievable visited sets; reason: walks may repeat vertices and arcs, s=t and zero-length walks are retained; the visited-set family is finite and feasible inputs attain its maximum
--   - encoding: O(n^ε) ratio and n^{O(1/ε)} runtime for every ε>0 → K_ε after ε, one absolute exponent c before ε, integer parameter k=max(1,ceil(2/ε)) and cost (n+1)^{ck}; reason: integer and large-ε runtime convention; it is O(1/ε) for 0<ε≤1 and a fixed polynomial for ε≥1; the program family is chosen before ε and never receives a real number
--   - encoding: combinatorial algorithm obtained from Algorithm 5 and the general-to-layered reduction → deterministic RAM output is exactly the defined reduction/Algorithm 5/reconstruction result; unit lengths choose only fixed connecting paths; reason: the unit lengths do not constrain output or comparison walks and are not a length bound; the final RAM cost covers all stages
-- source:
--   Lars Rohwedder, Rico Zenklusen, STOC 2027 submission #658 (October 2026), Theorem 15, p. 25 (PDF p. 26); reduction, p. 14 (PDF p. 15)

import Mathlib
import Definitions.Def_SubmodMDP_Policies_Supplement_Reduction

namespace SubmodMDP.Policies.Supplement

/-- Theorem 15, printed p. 25 (PDF p. 26). The algorithm is deterministic and combinatorial:
it implements the reduction followed by Algorithm 5 and fixed connecting paths. There is no
length function or budget in the input or in the optimum. The cost exponent c is absolute. -/
theorem theorem_15 :
    ∃ c : ℕ, 0 < c ∧ ∃ Alg : ℕ → Program, (∀ k, (Alg k).Deterministic) ∧
    ∀ ε : ℝ, 0 < ε → ∃ Kε : ℝ, 0 < Kε ∧
    ∀ (n : ℕ) (I : Ori n), (∃ W, Walk I.graph I.s I.t W) →
    ∀ f : Finset (Fin n) → ℚ, Reward f →
    let O : Oracle := ⟨n, f⟩
    let inp := encOri I
    let B := polyTime n (epsK ε) c
    Computes (Alg (epsK ε)) O (wordLen inp O) inp B
      (encOptionalWalk (combinatorialWalk I (epsK ε) f)) ∧
    ∃ W, combinatorialWalk I (epsK ε) f = some W ∧ Walk I.graph I.s I.t W ∧
      (optimum I f (fun _ => True) : ℝ) / (Kε * (n : ℝ) ^ ε) ≤ (f W.toFinset : ℝ) := by sorry

end SubmodMDP.Policies.Supplement
