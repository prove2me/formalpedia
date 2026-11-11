-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_proposition_3_8
-- name    : PostedPriceLimits.FullRevelation.proposition_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:36.478293+00:00
-- url     : https://prove2.me/theorems/8347f6bf-d9cc-4383-a845-f27b34a804fc
-- title:
--   Proposition 3.8 — biased XOS representations are XOS, with a clause oracle no more informative
-- statement:
--   Let $M=[m]$ and let $U\subseteq\mathbb R_+^{m+1}$ be a biased XOS representation of $v:2^M\to\mathbb R_+$, i.e. a finite nonempty set of clauses $(u_0,u)$ with nonnegative bias and item values such that
--   $$v(S)=\max_{(u_0,u)\in U}\{u(S)+u_0\mathbf 1(S\ne\varnothing)\}\qquad(S\subseteq M).$$
--   Then:
--   1. $v$ is XOS;
--   2. $v$ has an XOS representation $U'\subseteq\mathbb R_+^m$ whose clause-oracle responses are no more informative than the responses of some biased clause oracle of $U$: there is a single transformation, fixed in advance and independent of $v$, $U$ and $U'$, which maps each price query $p\in[0,\infty]^m$ and the biased oracle's response to $p$ to the response of the clause oracle of $U'$ to $p$.
--
--   This justifies working with biased XOS valuations in the lower-bound constructions: biased valuations are valid XOS valuations, and an oracle for an equivalent ordinary representation leaks no additional information.
--
--   Differences from the source:
--   - reading: the responses of the clause oracle given by U′ are no more informative than the responses of some biased clause oracle given by U → a single simulation map sim, chosen before v and U, with sim(p, biased response) equal to the U′-clause-oracle response for every query p; reason: if the simulation could depend on v or U′ the claim would be trivial (the clause-oracle response is a function of the demand set); the proof's map S,u ↦ w^{(u,max S)} is fixed in advance
--   - encoding: U ⊆ ℝ₊^{m+1} with coordinate 0 the bias; finite since maxima are taken → a nonempty Finset of pairs (u₀, u) with u₀ ≥ 0, u ≥ 0; reason: same objects; a maximum over U requires U finite and nonempty
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Proposition 3.8, p.6 (PDF 7), proof p.6 (PDF 7); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model
import Definitions.Def_PostedPriceLimits_FullRevelation_Model
import Definitions.Def_PostedPriceLimits_FullRevelation_BiasedXOS
open scoped ENNReal
open ComplementFreeCA.XOSGreedy

namespace PostedPriceLimits.FullRevelation

/-- Proposition 3.8. Let `U` be a biased XOS representation of `v : 2^M → ℝ₊`. Then
(1) `v` is XOS, and (2) `v` has an XOS representation `U'` whose clause-oracle responses are
no more informative than the responses of some biased clause oracle of `U`: there is one fixed
transformation `sim` (independent of `v`, `U`, `U'`) mapping each query and biased-oracle
response to the `U'`-clause-oracle response. -/
theorem proposition_3_8 (d : ℕ) :
    (∀ (v : Finset (Fin d) → ℝ) (U : Finset (ℝ × (Fin d → ℝ))), IsBiasedXOSRep U v → IsXOS v) ∧
    ∃ sim : (Fin d → ℝ≥0∞) → Finset (Fin d) × (ℝ × (Fin d → ℝ)) → Finset (Fin d) × (Fin d → ℝ),
      ∀ (v : Finset (Fin d) → ℝ) (U : Finset (ℝ × (Fin d → ℝ))), IsBiasedXOSRep U v →
        ∃ E : XOSExpr d, (∀ S, v S = E.val S) ∧
          ∃ orc : (Fin d → ℝ≥0∞) → Finset (Fin d) × (ℝ × (Fin d → ℝ)),
            IsBiasedClauseOracle U v orc ∧ ∀ p, IsXOSClauseResponse E p (sim p (orc p)) := by sorry

end PostedPriceLimits.FullRevelation
