-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_lemma_5_6
-- name    : ShortestPlanarDisjoint.Main.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:41:45.20981+00:00
-- url     : https://prove2.me/theorems/a5c8e8b0-caa1-4422-8785-71b0dff1fbbc
-- title:
--   Lemma 5.6 — Parallel graph queries
-- statement:
--   Fix the face count f, a weight exponent C, the coefficient c in k≤c log n and an exponent q bounding the number of deletion queries. For positive edge costs bounded by N^C and polynomially many edge-deleted subgraphs, all coefficients of the constructed query can be computed simultaneously in logspace-uniform NC². The circuits include seam construction and selector preprocessing and output full arrays through degree n N^C; every higher coefficient vanishes. All deletions retain the original cut, ports and selector.
--
--   The constructed cut also satisfies the unique selector system, existence and uniqueness of each nonzero reduced state with pairing preserved, equation (13), and every Section 4.1 query guarantee for all positive cost assignments and deletions. These are conclusions, not oracle assumptions.
--
--   Differences from the source:
--   - encoding: a supplied cellular embedding with corner assignments on a connected surface → a Fin-indexed signed rotation flag map with computed integer Euler genus, explicit corners and used-face labels; reason: this is the same finite cellular embedding up to barycentric realization, including both orientable and nonorientable cases; connectedness is necessary for cellularity, and isolated single-vertex spheres are retained
--   - encoding: uniform O bounds with fixed weight exponent and fixed logarithmic coefficient → uniform natural coefficients and exponents before instance data, N=max(2,n), k≤c ceil(log₂ N), and ceil(log₂(1/δ)) repetition envelopes; reason: natural exponents cover every fixed real exponent by rounding up; small cases have finite envelopes; no witness depends on a graph, optimum or random tape
--   - encoding: all graph-query coefficients, including preprocessing → a uniformly generated Boolean circuit returning a finite cut code and full coefficient arrays padded to the explicit degree envelope; reason: extra zero coefficients and the cut code change no query and remain polynomial in size; edge deletions retain the original embedding data
--   - generalization: Lemma 5.6's coefficient-computation assertion with the preceding Section 5.4 justification → the same computation together with the supporting exact selector, state-reduction, equation (13) and Section 4.1 correctness conclusions; reason: these are the preceding source claims and required proof obligations; the coefficient assertion is retained in full and none is moved to a hypothesis
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Lemma 5.6, p. 25 (PDF p. 27)

import Definitions.Def_ShortestPlanarDisjoint_Main_Query
set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
/-- Full coefficient computation in uniform NC², including the cut and selector
preprocessing, for polynomially many deletion queries at once. Query correctness,
unique reduced states and equation (13) are conclusions, not hypotheses. -/
theorem lemma_5_6 :
    ∀ (f C c q : ℕ), ∃ (F : UniformCircuitFamily) (A d : ℕ),
      LogspaceUniform F A d ∧
      (∀ n, (F.circuit n).size ≤ A * (max 2 n) ^ d ∧
        (F.circuit n).depth ≤ A * (logEnvelope n) ^ 2) ∧
      ∀ (n k : ℕ) (I : RoutingInput n k) (E : FaceInput I f)
          (gaps : E.GapChoice) (deleted : List (Finset I.Edge)),
        0 < k → E.IsCellular → E.embedding.IsPlanar →
        k ≤ c * logEnvelope n →
        (∀ e ∈ I.graph.edgeSet, 0 < I.weight e ∧ I.weight e ≤ (max 2 n)^C) →
        deleted.length ≤ (max 2 n)^q →
        let input := E.bits ++ gaps.bits ++ numberBits deleted.length ++ deleted.flatMap deletionBits
        input.length ≤ (F.circuit n).inputs ∧
        ∃ S : SeamCode E (f-1), S.RealizesCut gaps ∧ S.PlanarOrder gaps ∧ S.crossingCount ≤ A*n*f ∧
          S.QueryCorrect ∧
          (∀ removed ∈ deleted, ∀ z, n * (max 2 n)^C < z →
            (S.query removed I.weight).coeff z = 0) ∧
          (S.bits ++ S.queryBits deleted ((max 2 n)^C)).IsPrefix
            ((F.circuit n).eval
              (input ++ List.replicate ((F.circuit n).inputs-input.length) false)) := by sorry
end ShortestPlanarDisjoint.Main
