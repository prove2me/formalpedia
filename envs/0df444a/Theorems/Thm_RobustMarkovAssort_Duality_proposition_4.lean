-- Prove2me | Theorems.Thm_RobustMarkovAssort_Duality_proposition_4
-- name    : RobustMarkovAssort.Duality.proposition_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:17:17.200425+00:00
-- url     : https://prove2.me/theorems/aab9134c-6895-4474-b346-ca737fafb5b6
-- title:
--   Proposition 4 — deterministic general assortment and dual equality
-- statement:
--   Under Assumptions 3 and 4, fix any admissible parameter u. There exists a real z which is both the greatest value of lambda(u) dot v over all assortments S and their balance-feasible vectors v, and the least value over v>=r satisfying A(u)v>=b(u). Thus the attained values of (9) and (10) agree. The vector b(u) is arbitrary real data.
--
--   Differences from the source:
--   - encoding: products numbered 1 through n and arbitrary subsets of N → products Fin n and assortments Finset (Fin n); reason: the index shift is a bijection and every subset is represented
--   - generalization: a finite universe of products → n may also be zero; reason: the empty universe has one empty vector and one assortment, all revenues are zero, and every claimed extremum and fixed point exists uniquely there
--   - reading: uncertainty sets of possible model parameters → each parameter set is explicitly nonempty; reason: a possible-parameter set is read as containing at least one scenario, consistent with the choice of u0 on page 19
--   - encoding: the displayed min and max values → IsLeast and IsGreatest objective-image relations, including every inner extremum; reason: membership expresses attainment and the order bound expresses optimality
-- source:
--   Désir, Goyal, Jiang, Xie and Zhang, Robust Assortment Optimization Under the Markov Chain Choice Model, Operations Research (2023), DOI 10.1287/opre.2022.2420; canonical artifact PDF/printed p. 14, Proposition 4

import Definitions.Def_RobustMarkovAssort_Duality_GeneralPrograms

namespace RobustMarkovAssort.Duality

theorem proposition_4 {n : ℕ} {α : Type*} (G : GeneralModel n α)
    (h3 : Assumption3 G) (h4 : Assumption4 G) (u : α) (hu : u ∈ G.U) :
    ∃ z : ℝ,
      IsGreatest {t | ∃ (S : Assortment n) (v : Vec n),
        Balance G.r (G.A u) (G.b u) S v ∧ t = ∑ i, G.lam u i * v i} z ∧
      IsLeast {t | ∃ v : Vec n, DualFeasible G u v ∧ t = ∑ i, G.lam u i * v i} z := by sorry

end RobustMarkovAssort.Duality
