-- Prove2me | Theorems.Thm_SemAC02_Supplement_lemma_7_1_random_logwidth_expansion
-- name    : SemAC02.Supplement.lemma_7_1_random_logwidth_expansion
-- status  : Proved
-- author  : @Henry Yuen
-- created : 2026-11-18T10:10:31.72444+00:00
-- url     : https://prove2.me/theorems/284a7c30-f9ab-48f4-9418-619b3cb306bd
-- title:
--   Lemma 7.1: random logarithmic-width CNFs are unsatisfiable boundary expanders
-- statement:
--   Put $\ell=\lceil\log_2 n\rceil$ and $m=n2^\ell$. Sample $m$ clauses independently and uniformly, with repetition, from the clauses of width exactly $\ell$ on distinct variables among $n$ Boolean variables. Let $F_n$ be their conjunction. For a set $J$ of clause indices, write $N(J)$ for its neighboring variables and $\partial(J)$ for the variables occurring in exactly one of the indexed clauses.
--
--   There is an absolute constant $\eta>0$ such that, with probability tending to one as $n\to\infty$, $F_n$ is unsatisfiable and simultaneously every nonempty set $J$ of at most $\lfloor\eta n/\ell\rfloor$ clause indices satisfies
--
--   $$
--   |N(J)|\ge\frac{3\ell}{4}|J|,\qquad |\partial(J)|\ge\frac{\ell}{2}|J|.
--   $$
--
--   This supplies the common expansion event used to prove the bounded-bottom-degree lower bounds for random logarithmic-width CNFs.
--
--   **Formalization Note** The graph keeps the sampled clause indices, so repeated clauses remain distinct left vertices. The CNF itself is the set of sampled clauses, which preserves satisfiability. Neighborhoods and boundaries are written directly as finite sets. The ceiling logarithm is `Nat.clog`, and probability is the mission's uniform counting probability.
-- source:
--   Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, Lemma 7.1, printed p.51 (PDF p.53), with proof in Appendix C, printed p.72 (PDF p.74), equations (55)–(56). https://www.doc.ic.ac.uk/~itzamere/Reslin_Simplification.pdf. Verified against the public manuscript saved in sources/Hard_Instances_Semantic.pdf; public and mission-pinned manuscript hashes differ as recorded in README.md.

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_SemAC02_Supplement_randCNF
open Filter Topology LiftSAParity SemAC02.Supplement

theorem SemAC02.Supplement.lemma_7_1_random_logwidth_expansion :
    ∃ η : ℝ, 0 < η ∧ Tendsto (fun n : ℕ => uprob
      (fun ω : Fin (n*2^Nat.clog 2 n) → WClause n (Nat.clog 2 n) =>
        ¬ Satisfiable (seqCNF ω) ∧ ∀ J : Finset (Fin (n*2^Nat.clog 2 n)),
          J.Nonempty → J.card ≤ ⌊η*n/(Nat.clog 2 n : ℝ)⌋₊ →
          (3 : ℝ)*(Nat.clog 2 n)*J.card/4 ≤
              ((J.biUnion (fun j => (ω j).1.image Prod.fst)).card : ℝ) ∧
          ((Nat.clog 2 n : ℝ)/2)*J.card ≤
              ((Finset.univ.filter (fun v : Fin n =>
                (J.filter (fun j => v∈(ω j).1.image Prod.fst)).card=1)).card : ℝ))) atTop (𝓝 1) := by sorry
