-- Prove2me | Theorems.Thm_QuantumBipartiteTesting_Bipartiteness_Supplement_lemma_4_7
-- name    : QuantumBipartiteTesting.Bipartiteness.Supplement.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:16:54.198698+00:00
-- url     : https://prove2.me/theorems/a13dea0d-9c17-446b-b011-3ca955e3b17e
-- title:
--   Lemma 4.7 — Exact coherent replacement oracle simulation using at most 2q queries
-- statement:
--   Fix a positive color count, a simple cubic cloud, a packed ordering of its three neighbors, and a bijective labeling of the product vertices, all independently of $H$. The replacement edge set is a simple graph of maximum degree four, and its specified three-internal-then-external oracle is a packed representation, for every consistent $H$.
--
--   For every finite complex $q$-query algorithm $A$ using any injective XOR answer encoding for the replacement graph, and every such encoding for the intermediate graph, there is a finite complex algorithm $B$ with $q'\le2q$, independent of $H$, such that
--   $$\Pr[B^H\text{ accepts}]=\Pr[A^{R(H)}\text{ accepts}]\quad\text{for every consistent }H.$$
--   The difference of expected acceptance probabilities under any two probability laws supported on consistent intermediate graphs is also exactly preserved. In particular, the distinguishing advantage is unchanged. This is a coherent quantum reduction with arbitrary finite workspace, not a simulation limited to classical queries.
--
--   Differences from the source:
--   - encoding: quantum algorithms and corresponding replacement graphs → published finite complex circuits, fixed encodings and packed cloud ports, plus explicit construction-validity conclusions; reason: the source pp.23–25 supplies the simplicity, degree and oracle facts; these are conclusions, and gates remain input-independent
--   - generalization: the intermediate graphs from the sampling construction → every consistent matching-colored multigraph; reason: the pointwise coherent simulation uses only the color-port rule, so it specializes to every sampled graph
--   - generalization: the replacement construction uses an expanding cubic cloud → any simple cubic cloud, without a cloud expansion hypothesis; reason: the exact compute-copy-uncompute simulation and construction-validity facts use only cubicity and fixed cloud ports; every source cloud is included
-- source:
--   Chandrima Kayal, Sayantan Sen, Dániel Szabó, STOC 2027 submission #878 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/878.pdf, Lemma 4.7, printed page = PDF page 24

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Supplement_Unsigned

namespace QuantumBipartiteTesting.Bipartiteness.Supplement
open Finset

theorem lemma_4_7 {n c k w q kH : ℕ} (hc : 0 < c)
    (e : Fin (n*c) ≃ Fin n × Fin c) (J : Finset (Edge c)) (hJ : Cubic J)
    (P : Fin c × Fin 3 → Option (Fin c)) (hP : Represents J P)
    (E : Encoding (Fin (n*c)) k) (EH : Encoding (Fin n) kH)
    (A : Algorithm (Address (n*c) 4) k w q)
    (out : (Address (n*c) 4 × Bits k) × Fin w → Bool) :
    (∀ H : Finset (ColoredEdge n c), Consistent H →
      IsGraph (Replacement e J H) ∧ DegreeBound 4 (Replacement e J H) ∧
      Represents (Replacement e J H) (ReplacementOracle e P H)) ∧
    ∃ w' q' : ℕ, q' ≤ 2*q ∧ ∃ B : Algorithm (Address n c) kH w' q',
      ∃ outB : (Address n c × Bits kH) × Fin w' → Bool,
        (∀ H : Finset (ColoredEdge n c), Consistent H →
          Accept EH B outB (LiftOracle (UnsignedResponse H)) =
          Accept E A out (LiftOracle (ReplacementOracle e P H))) ∧
        (∀ μ ν : Finset (ColoredEdge n c) → ℝ,
          (∀ H, 0 ≤ μ H ∧ 0 ≤ ν H) → (∑ H, μ H) = 1 → (∑ H, ν H) = 1 →
          (∀ H, ¬ Consistent H → μ H = 0 ∧ ν H = 0) →
          (∑ H, μ H * Accept EH B outB (LiftOracle (UnsignedResponse H))) -
            (∑ H, ν H * Accept EH B outB (LiftOracle (UnsignedResponse H))) =
          (∑ H, μ H * Accept E A out (LiftOracle (ReplacementOracle e P H))) -
            (∑ H, ν H * Accept E A out (LiftOracle (ReplacementOracle e P H)))) := by sorry

end QuantumBipartiteTesting.Bipartiteness.Supplement
