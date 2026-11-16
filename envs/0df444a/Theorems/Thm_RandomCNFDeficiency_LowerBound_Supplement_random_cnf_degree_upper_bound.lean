-- Prove2me | Theorems.Thm_RandomCNFDeficiency_LowerBound_Supplement_random_cnf_degree_upper_bound
-- name    : RandomCNFDeficiency.LowerBound.Supplement.random_cnf_degree_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:00:34.075104+00:00
-- url     : https://prove2.me/theorems/4334558f-497e-43a8-b14f-ac5e62872253
-- title:
--   Theorem 4.1 — random $k$-CNFs are refutable in degree $r+1$ over every field
-- statement:
--   Let $k=k(n)$ satisfy $\omega_n(1)\le k\le O(\log n)$ and put
--
--   $$M=n2^k,\qquad r=\frac n2-\frac n{2k}\ln\frac k{32}.$$
--
--   Let $F$ consist of $M$ independently sampled uniform signed $k$-clauses on $n$ variables. With probability $1-o_n(1)$ the formula $F$ is unsatisfiable and
--
--   $$\operatorname{Deg}_{\mathrm{PC},\mathbb F}(F)\le r+1$$
--
--   holds over every field $\mathbb F$ simultaneously. More precisely, for all sufficiently large $n$ this event has probability at least $1-e^{-(1-\ln2)n}-2^{-n}$ (Equation (43)). In particular there is an absolute constant $C>0$ such that, for every such sequence $k$ and all large $n$, on the same event
--
--   $$\operatorname{Deg}_{\mathrm{PC},\mathbb F}(F)\le\frac n2-\frac{n\ln k}{2k}+C\frac nk$$
--
--   over every field.
--
--   This is the quantitative form of Theorem 1.3. It shows that the lower bound of Theorem 1.1, $n/2-4n/\sqrt k$, is close to tight, and that random $k$-CNFs cannot give $\mathrm{AC}^0[p]$-Frege lower bounds beyond depth two through the degree–size tradeoff of Appendix A.
--
--   Differences from the source:
--   - encoding: variables x_1, …, x_n → Fin n with true representing 1; reason: the bijection i ↦ i+1 preserves every clause and assignment
--   - encoding: ω_n(1) ≤ k ≤ O(log n) → the published LogarithmicRegime k: k → ∞ and, for some C > 0, eventually 1 ≤ k ≤ n and k ≤ C log₂ n; reason: k ≤ C log₂ n already forces k ≤ n and divergence forces k ≥ 1 eventually; same regime
--   - encoding: F consists of M = n2^k independent uniform signed k-clauses → the published sampleProbability: uniform product mass on ordered M-tuples of published ProperClause n k, read as a clause set; reason: the same sampling law with replacement
--   - encoding: with probability 1 − o_n(1), F is unsatisfiable and Deg_PC,𝔽(F) ≤ r + 1 over every field → the probability of the event (F unsatisfiable and, for every field in one universe, some PC refutation of degree ≤ r + 1) tends to 1; reason: one event for all fields simultaneously, as in the source
--   - generalization: probability 1 − o_n(1) → additionally, eventually the probability is at least 1 − e^{−(1−ln 2)n} − 2^{−n}; reason: this is Equation (43) of the source's proof and implies 1 − o_n(1)
--   - reading: with the same probability, Deg_PC,𝔽(F) ≤ n/2 − n ln k/(2k) + O(n/k) over every field (35) → there is one absolute C > 0, chosen before the sequence k, such that eventually every F in the same event has, over every field, a refutation of degree ≤ n/2 − n ln k/(2k) + C n/k; reason: the source does not say whether the O-constant may depend on the sequence k; the stronger, absolute reading is taken (the proof gives r + 1 ≤ n/2 − n ln k/(2k) + n ln 32/(2k) + 2); the event inclusion gives the same probability
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Theorem 4.1, Equations (33)–(35), printed p. 15, PDF p. 17; Equations (42)–(43), printed pp. 18–19, PDF pp. 20–21; Theorem 1.3, printed p. 2, PDF p. 4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_UpperModel
universe uUpperThm
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound

/-- Conneryd, STOC 2027 #332, Theorem 4.1 (= Theorem 1.3): with `M = n 2^k` and
`r = n/2 - (n/(2k)) ln(k/32)`, a random `k`-CNF is unsatisfiable and has PC refutations of
degree at most `r + 1` simultaneously over every field, with probability `1 - o(1)`
(explicitly at least `1 - e^{-(1 - ln 2) n} - 2^{-n}` eventually, Equation (43)); on the same
event the degree is at most `n/2 - n ln k/(2k) + C n/k` over every field (Equation (35)),
with one constant `C > 0` for every admissible sequence `k`. -/
theorem random_cnf_degree_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ → ℕ, LogarithmicRegime k →
      Filter.Tendsto
          (fun n => sampleProbability n (k n) (UpperEvent.{uUpperThm} n (k n)))
          Filter.atTop (nhds 1) ∧
      (∀ᶠ n : ℕ in Filter.atTop,
        1 - upperFailureBound n ≤
          sampleProbability n (k n) (UpperEvent.{uUpperThm} n (k n))) ∧
      ∀ᶠ n : ℕ in Filter.atTop, ∀ F : CNF n,
        UpperEvent.{uUpperThm} n (k n) F →
          AllFieldsEasy.{uUpperThm} F (upperAsymptoticBound C n (k n)) := by sorry

end RandomCNFDeficiency.LowerBound.Supplement
