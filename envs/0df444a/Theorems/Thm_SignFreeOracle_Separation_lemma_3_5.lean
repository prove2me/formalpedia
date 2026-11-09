-- Prove2me | Theorems.Thm_SignFreeOracle_Separation_lemma_3_5
-- name    : SignFreeOracle.Separation.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:37.10837+00:00
-- url     : https://prove2.me/theorems/b0af477c-ef66-4f55-b090-08ccdf76006b
-- title:
--   Lemma 3.5 — explicitly constructible high-degree, high-girth base graphs
-- statement:
--   There is a single explicitly constructible sequence of connected simple $n$-regular graphs $B_n$, defined for every sufficiently large integer $n$, whose vertex counts $N_B$ and girths satisfy
--   $$2^{n^3\log_2^2n}\le N_B\le2^{2n^3\log_2^2n},\qquad \operatorname{girth}(B_n)\ge100n^{5/2}\log_2n.$$
--   Explicit construction means that one finite machine, on unary $n$, halts with the vertex count and the full adjacency table; no further complexity bound is stated in the manuscript. The threshold in $n$ is uniform. This supplies the actual connected regular base graphs used in the decorations; no fixed-degree expander surrogate is used.
--
--   Differences from the source:
--   - reading: logarithms have no specified base → binary logarithms in the construction and entropy estimates; reason: consistent with binary labels and the bit entropy bound; the closure estimate also holds with log2
--   - encoding: explicitly constructible graph sequence → one finite terminating transducer prints the vertex count and adjacency table; reason: the statement specifies no construction runtime; a uniform finite algorithm is retained
-- source:
--   Hamoudi, Le Borgne, Teganahally Sridhara, Quantum Advantage with Sign-Free Proofs: An Oracle Separation between StoqMA and MA, STOC 2027 submission #601 (October 2026), Lemma 3.5, p. 10 (PDF p. 10)

import Definitions.Def_SignFreeOracle_Separation_Family
import Definitions.Def_SignFreeOracle_Separation_Encoding

set_option autoImplicit false

namespace SignFreeOracle.Separation

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- Explicit construction means a single terminating finite machine prints each graph's
vertex count and adjacency table, with no extra runtime bound asserted by the source. -/
theorem lemma_3_5 :
    ∃ (N : ℕ → ℕ) (B : ∀ n, SimpleGraph (Fin (N n))) (M : OTM) (n₀ : ℕ),
      ∀ n, n₀ ≤ n → BaseConditions n (N n) (B n) ∧
        ∃ T : ℕ, M.result (fun _ => false) (List.replicate n true) T ≠ none ∧
          M.output (fun _ => false) (List.replicate n true) T =
            codeNat (N n) ++ ((List.finRange (N n)).flatMap fun u =>
              (List.finRange (N n)).map fun v => @decide ((B n).Adj u v) (Classical.propDecidable _)) := by sorry

end SignFreeOracle.Separation
