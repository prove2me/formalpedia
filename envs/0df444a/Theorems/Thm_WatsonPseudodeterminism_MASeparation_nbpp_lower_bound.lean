-- Prove2me | Theorems.Thm_WatsonPseudodeterminism_MASeparation_nbpp_lower_bound
-- name    : WatsonPseudodeterminism.MASeparation.nbpp_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:41:21.385706+00:00
-- url     : https://prove2.me/theorems/4be8d3be-5d6f-44e5-b704-f4998bfd5334
-- title:
--   §4 — Square-root lower bound at error 0.01
-- statement:
--   Let $F_n=f_n\circ g^n$ be the separating function, with $h(n)=100\lceil\log_2n\rceil$ and admissible sizes $n=4s^2$, $s\ge1$. There is a natural threshold $n_0$ such that for every admissible $n\ge n_0$ and every natural $d$,
--
--   $$d\le0.01\sqrt n\quad\Longrightarrow\quad F_n\text{ has no }0.01\text{-error N·BPP-type protocol of cost }d.$$
--
--   The quantified protocols retain both the depth bound and the bound of $2^d$ witnesses, with a pseudodeterministic acceptance gap only on valid inputs. This is the explicit lower bound proved by §4. Together with uniform constant-error amplification it rules out every polylogarithmic standard-error N·BPP cost along this family.
--
--   Differences from the source:
--   - reading: h = 100 log n → h = 100 * Nat.clog 2 n, with logarithms to base two; reason: block lengths are integral; rounding upward preserves the small-discrepancy regime specified in the brief
--   - reading: the implicit infinite sequence of even square sizes in §4 → n = 4s² for a positive natural s; reason: this fixes one infinite sequence on which both halves and the square-root block steps are integral
--   - encoding: a set of at most 2^d distributions over depth-d protocols → an indexed family of k PMFs with k ≤ 2^d and support depth at most d; reason: duplicate indices do not change the represented set; every source distribution is represented and zero-mass trees do not affect the law
--   - reading: the proof assumes cost d = 0.01√n and uses asymptotic numerical estimates → for all sufficiently large admissible n, every natural d ≤ 0.01√n is impossible; reason: bounded-depth protocols can be padded to a larger budget; integrality and the large-size inequalities are made explicit
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §4, “F ∉ NP^BPP = N·BPP”, pp. 10–14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_SeparatingFunction

namespace WatsonPseudodeterminism.MASeparation

/-- §4, pp. 10–14: asymptotic lower bound for the 0.01-error N·BPP model. -/
theorem nbpp_lower_bound :
    ∃ n₀ : ℕ, ∀ n : ℕ, Admissible n → n₀ ≤ n → ∀ d : ℕ,
      (d : ℝ) ≤ (0.01 : ℝ) * Real.sqrt (n : ℝ) →
      ¬ NBPPProtocolErr (0.01 : ℝ) (liftedFn n) d := by sorry

end WatsonPseudodeterminism.MASeparation
