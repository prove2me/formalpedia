-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_lemma_2_10
-- name    : QuantumBipartiteTesting.Bipartiteness.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:13:23.063607+00:00
-- url     : https://prove2.me/theorems/f785fdd3-88a8-4526-8da6-f5737a5bf143
-- title:
--   Lemma 2.10 — canonical coefficient bounds
-- statement:
--   For any actual finite $q$-query circuit and any compatible canonical response table $T$ of size $k$, its interpolation coefficient obeys
--   $$|a_T|\le2^k.$$
--   For fixed query and response count constants $a,b$, there is $C(a,b)>0$ such that, whenever $N\ge2$, the query set has at most $aN$ elements and the non-null response set has at most $bN$ elements,
--   $$\sum_T|a_T|\le\exp(C(a,b)q\log N).$$
--   All encodings, circuits, workspace sizes and query counts are quantified after the constant. This includes the source's degree-three signed graph oracle, with a linear number of queries and responses, and bounds the amplification of monomial expectation errors.
--
--   Differences from the source:
--   - encoding: finite quantum query circuits with binary encoded outcomes and arbitrary workspace → published QueryAlg, arbitrary finite complex registers, injective null-zero bit encoding, unitary XOR oracle, input-independent output event; reason: every finite workspace is represented up to a basis bijection; unused answer bit strings and dummy vertex queries are retained
--   - encoding: O(N) response and query counts in the lemma and page-30 proof → fixed constants a,b bound both cardinalities; C depends only on a,b; N>=2; reason: expands the source asymptotic convention and excludes only small sizes where log N does not express that convention
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), Lemma 2.10, PDF = printed page 11. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction

namespace QuantumBipartiteTesting.Bipartiteness
open Finset

theorem lemma_2_10 :
    (∀ (I S : Type) [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S],
      ∀ k w q : ℕ, ∀ E : Encoding S k, ∀ A : Algorithm I k w q,
      ∀ out : (I × Bits k) × Fin w → Bool, ∀ T : ResponseTable I S,
        |CanonicalCoeff E A out T| ≤ (2 : ℝ) ^ T.val.card) ∧
    (∀ a b : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ (I S : Type) [Fintype I] [Fintype S] [DecidableEq I] [DecidableEq S],
      Fintype.card I ≤ a*N → Fintype.card S ≤ b*N →
      ∀ k w q : ℕ, ∀ E : Encoding S k, ∀ A : Algorithm I k w q,
      ∀ out : (I × Bits k) × Fin w → Bool,
        (∑ T : ResponseTable I S, |CanonicalCoeff E A out T|) ≤ Real.exp (C*q*Real.log N)) := by sorry

end QuantumBipartiteTesting.Bipartiteness
