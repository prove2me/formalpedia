-- Prove2me | Theorems.Thm_RobustMarkovAssort_Duality_claim_1
-- name    : RobustMarkovAssort.Duality.claim_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:17:09.953111+00:00
-- url     : https://prove2.me/theorems/8e572206-94cc-42bb-8d04-cdf3caec995d
-- title:
--   Claim 1 — unique feasible vector of the separated balance program
-- statement:
--   Under the standing Assumptions 3–6 of the proof of Theorem 2, every assortment S has exactly one real vector v satisfying (16): v_i=r_i on S, and off S, v_i is the attained minimum over u of the general row expression. Existence and uniqueness are both asserted.
--
--   Differences from the source:
--   - encoding: products numbered 1 through n and arbitrary subsets of N → products Fin n and assortments Finset (Fin n); reason: the index shift is a bijection and every subset is represented
--   - generalization: a finite universe of products → n may also be zero; reason: the empty universe has one empty vector and one assortment, all revenues are zero, and every claimed extremum and fixed point exists uniquely there
--   - reading: uncertainty sets of possible model parameters → each parameter set is explicitly nonempty; reason: a possible-parameter set is read as containing at least one scenario, consistent with the choice of u0 on page 19
--   - reading: equivalent optimization programs with nested minima in Assumptions 5 and 6 → equal attained least objective values with inner weight minima defined on the relational feasible domain; reason: this makes optimal-value equivalence explicit without requiring pointwise simultaneous optimizers; missing row minima do not receive defaults
--   - encoding: the displayed min and max values → IsLeast and IsGreatest objective-image relations, including every inner extremum; reason: membership expresses attainment and the order bound expresses optimality
-- source:
--   Désir, Goyal, Jiang, Xie and Zhang, Robust Assortment Optimization Under the Markov Chain Choice Model, Operations Research (2023), DOI 10.1287/opre.2022.2420; canonical artifact PDF/printed p. 19, Claim 1

import Definitions.Def_RobustMarkovAssort_Duality_GeneralPrograms

namespace RobustMarkovAssort.Duality

theorem claim_1 {n : ℕ} {α : Type*} (G : GeneralModel n α)
    (h3 : Assumption3 G) (h4 : Assumption4 G)
    (h5 : Assumption5 G) (h6 : Assumption6 G) (S : Assortment n) :
    ∃! v : Vec n, SeparatedBalance G S v := by sorry

end RobustMarkovAssort.Duality
