-- Prove2me | Theorems.Thm_PfaffianRecognition_Recognition_Supplement_theorem_3_7
-- name    : PfaffianRecognition.Recognition.Supplement.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:02:39.361734+00:00
-- url     : https://prove2.me/theorems/ed259688-1198-4227-bf1f-443397cdc710
-- title:
--   Theorem 3.7 — randomized search for two perfect matchings of opposite signs
-- statement:
--   There is one randomized machine $\mathcal M$ reading fair random bits, and constants $C\ge1$, $k$, fixed before all inputs, such that for every finite simple graph $G$ on $\{0,\dots,N-1\}$ and every orientation $D$ of $G$, with input $w$ the encoding of $(G,D)$ and budget $B=C\,(|w|+2)^k$:
--
--   1. on every random tape of length $B$, $\mathcal M$ halts within $B$ steps using at most $B$ random bits;
--   2. if $D$ is non-Pfaffian, then with probability at least $1/2$ over the $B$ fair bits, the output of $\mathcal M$ is the encoding of a pair $(M_1,M_2)$ of perfect matchings of $G$ with
--   $$
--   \operatorname{sign}_D(M_1)\ne\operatorname{sign}_D(M_2).
--   $$
--
--   Such a pair certifies that $D$ is non-Pfaffian; the theorem turns the randomized test of Theorem 3.2 into a certificate finder.
--
--   **Formalization Note** The machine model, input encoding, step and tape budget and fair-bit probability are those of the published computation model (as in `InCoRP`). The output is the concatenation of the two $N^2$ row-major edge-indicator vectors of $M_1$ and $M_2$ (`matchingBits`).
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graph G → SimpleGraph (Fin N) for every N, vertices in a fixed order; reason: every finite simple graph has such a labelling; no instance is removed
--   - encoding: randomized polynomial time algorithm → one CoinMachine with RunsWithin under the single bound B = C·(|w|+2)^k (1 ≤ C) on steps and random bits, probability by fairProb over B fair bits; reason: the published bit-machine model of the base mission; polynomial time with no prescribed exponent
--   - encoding: finds two perfect matchings of opposite signs → output equals matchingBits M₁ ++ matchingBits M₂ for perfect matchings with matchingSign D M₁ ≠ matchingSign D M₂; reason: signs are ±1, so different means opposite; the encoding is injective
--   - reading: polynomial time algorithm given a non-Pfaffian orientation → the time and tape bound holds on every tape for every graph/orientation input, Pfaffian or not; reason: the usual meaning of a polynomial time algorithm on its input domain (graphs with orientations); the stronger of the two readings
-- source:
--   Priyanshu Pant, Ranveer Singh, Pfaffian Recognition is in coRP, STOC 2027 submission #858 (October 2026), Theorem 3.7, p. 11 (proof pp. 11–12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/858.pdf

import Definitions.Def_PfaffianRecognition_Recognition_computation_model

namespace PfaffianRecognition.Recognition.Supplement

open PfaffianRecognition.Recognition

/-- Theorem 3.7, p. 11 (proof pp. 11–12). One fair-bit machine and one polynomial bound, fixed
before all inputs: on every graph/orientation encoding and every tape it halts within the bound;
on a non-Pfaffian orientation, with probability at least 1/2 its output is the encoding of two
perfect matchings of `G` of opposite signs. -/
theorem theorem_3_7 :
    ∃ M : HypergraphUnreliability.FPRAS.CoinMachine, ∃ C k : ℕ, 1 ≤ C ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (D : Orientation G),
        let w := orientedGraphBits D
        let B := C * (w.length + 2) ^ k
        (∀ ω : Fin B → Bool, ∃ out : List Bool,
          M.RunsWithin w (HypergraphUnreliability.FPRAS.tapeList ω) B out) ∧
        (¬ IsPfaffianOrientation D → (1 / 2 : ℝ) ≤ HypergraphUnreliability.FPRAS.fairProb B
          (fun ω => ∃ M₁ M₂ : Finset G.edgeSet,
            MulmuleyVV.Matching.IsPerfectMatchingEdges G M₁ ∧
            MulmuleyVV.Matching.IsPerfectMatchingEdges G M₂ ∧
            matchingSign D M₁ ≠ matchingSign D M₂ ∧
            M.RunsWithin w (HypergraphUnreliability.FPRAS.tapeList ω) B
              (CatalyticMatching.General.matchingBits M₁ ++
                CatalyticMatching.General.matchingBits M₂))) := by sorry

end PfaffianRecognition.Recognition.Supplement
