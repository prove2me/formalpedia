-- Prove2me | Theorems.Thm_UnaryParityLifting_Exact_Supplement_coefficient_lower_bound
-- name    : UnaryParityLifting.Exact.Supplement.coefficient_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:48:24.244014+00:00
-- url     : https://prove2.me/theorems/016160df-8f9e-47bf-ab98-ceb8422ce503
-- title:
--   Theorem 5.1 — Quantitative Sink-of-DAG coefficient lower bound
-- statement:
--   Let F_n be the standard binary Sink-of-DAG contradiction on an n²×n² grid and N(n)=n⁴ceil(log₂(n²+1)) its actual bit count. There are fixed a,b∈(0,1), C>0, a natural K and n₀≥2 such that, simultaneously for every n≥n₀, F_n has width at most C log n and a Resolution refutation with at most C(n+1)^K lines and width at most C log n. Every general real formal SA refutation q of F_n of degree at most N(n)^a has a collected coefficient satisfying
--
--   $$|\operatorname{coefficient}(q)|\ge\exp(N(n)^b).$$
--
--   The coefficient may be a monomial coefficient in any signed axiom or Boolean-axiom multiplier, or a collected conical weight. The formal identity includes all Boolean axioms, and degrees are measured before cancellation. This retains all three clauses of the quantitative coefficient-hardness theorem; no certificate-nonexistence hypothesis is used. The source justifies any fixed 0<a<1/16 and 0<b<1/4 eventually, while the statement retains its existential a,b formulation.
--
--   Differences from the source:
--   - encoding: standard binary grid and asymptotic notation → the concrete bit CNF on Fin N and positive uniform constants with a common eventual threshold; reason: a bijective variable renaming and explicit quantifiers preserve every family instance and all asymptotic clauses
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), printed/PDF p.18, Theorem 5.1

import Definitions.Def_UnaryParityLifting_Exact_Supplement_generalSA
import Definitions.Def_UnaryParityLifting_Exact_Supplement_sinkDAG
import Definitions.Def_UnaryParityLifting_Exact_Supplement_resolution

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Theorem 5.1, including both Resolution upper bounds and general-real coefficient hardness. -/
theorem coefficient_lower_bound :
  ∃ a b C : ℝ, 0 < a ∧ a < 1 ∧ 0 < b ∧ b < 1 ∧ 0 < C ∧
    ∃ K n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      (((sinkDAG n).sup Finset.card : ℕ) : ℝ) ≤ C * Real.log n ∧
      (∃ p, Resolution (sinkDAG n) p ∧
        (p.length : ℝ) ≤ C * (n + 1 : ℝ) ^ K ∧
        (resolutionWidth p : ℝ) ≤ C * Real.log n) ∧
      (∀ q : GeneralSA (sinkDAG n), q.Valid →
        q.DegreeLE ((baseVariables n : ℝ) ^ a) →
        q.HasLargeCoefficient (Real.exp ((baseVariables n : ℝ) ^ b))) := by sorry

end UnaryParityLifting.Exact.Supplement
