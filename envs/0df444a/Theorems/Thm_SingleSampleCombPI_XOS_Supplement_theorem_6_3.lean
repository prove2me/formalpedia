-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_Supplement_theorem_6_3
-- name    : SingleSampleCombPI.XOS.Supplement.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:52:41.594989+00:00
-- url     : https://prove2.me/theorems/13b45c08-aa49-4bec-be0d-70ad7b61d8e0
-- title:
--   Theorem 6.3 — Every-ell integral multi-unit XOS SSCombPI with polynomial oracle complexity
-- statement:
--   For every integer $\ell\ge1$ and all finite numbers of buyers and item types, the source Algorithms 3/5/8 construction gives a feasible integral multi-unit allocation: at most one unit of each type per buyer, and at most $\ell$ per type overall. In every adversarial-order single-sample GoG instance of normalized monotone XOS buyers,
--   $$\mathbb E[\mathrm{Alg}]\ge\frac1{6\sqrt3}\mathbb E[\mathrm{Opt}_{\ell}(r)].$$
--   One uniform polynomial bounds primitive operations, original demand queries and original supporting-price queries. The vertex tie rule of Algorithm 5 and the $1/\ell$-grid invariant of Algorithm 8 are used. Only recorded blocks are sorted; zero padding is compressed, so the unit-cost bound does not expand the potentially large number of copies.
--
--   Differences from the source:
--   - encoding: the source divisible capped extension with its included original supporting clauses → the canonical finite representation by every given original supporting vector, zeroed outside its bundle; reason: this is an XOS representation of the same original valuation at every bundle, and makes ell*q(S) available at every source vertex; no XOS expression is extra input to the online algorithm
--   - encoding: ell identical units, at most one per buyer per type, Algorithms 3/5/8 → scaled vertex allocations in the divisible composition, multiplied by ell, with binary output and supply ell asserted in the theorem; reason: a single demand query chooses the Appendix F maximizing vertex; sorting actual history and indexed zero padding avoids a pseudopolynomial expansion; ell is unit-cost data with the usual encoding overhead
--   - encoding: expectations over the specified independent random choices → explicit fair finite GoG averages and nonnegative expectations over independent algorithm seeds; reason: these are ordinary expectations for measurable source payoffs; no input distribution or finite-support restriction is imposed
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Theorem 6.3, printed p. 33 / PDF p. 35; proof printed 43–44 / PDF 45–46.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Multi

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- Theorem 6.3, PDF 35 / printed 33; Appendix F, PDF 45–46. Every ell,
binary per-buyer output, the named components, and polynomial operations and
original demand/supporting queries, uniformly without expanding ell blocks. -/
theorem theorem_6_3 : ∃ K : ℕ, ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ n m : ℕ,
    (∀ H π ωs ρ s r, (∀ i, XOSBuyer (s i)) → (∀ i, XOSBuyer (r i)) →
      MultiFeasible ℓ (multiOut ℓ n m H π ωs ρ s r) ∧
      Cost.PolyBounded (alg3Cost (multiGreedy ℓ n m) (alg8 n) H π () ωs ρ
        (fun i => extendBuyer ℓ (s i)) (fun i => extendBuyer ℓ (r i)) + (n*m,0,0)) K (n+m)) ∧
    ∀ V : Fin n → Fin 2 → Buyer m, (∀ i t, XOSBuyer (V i t)) → ∀ ρ,
      ENNReal.ofReal (1/(6*Real.sqrt 3)) * avg (fun c : Fin n → Bool =>
        ENNReal.ofReal (multiOpt ℓ (fun i => (gogPair (V i) (c i)).2))) ≤
        multiExp ℓ V ρ := by sorry

end SingleSampleCombPI.XOS.Supplement
