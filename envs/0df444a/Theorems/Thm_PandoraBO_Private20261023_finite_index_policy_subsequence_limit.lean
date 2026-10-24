-- Prove2me | Theorems.Thm_PandoraBO_Private20261023_finite_index_policy_subsequence_limit
-- name    : PandoraBO.Private20261023.finite_index_policy_subsequence_limit
-- status  : Proved
-- author  : @QianJaneXie
-- created : 2026-10-24T01:23:11.017985+00:00
-- url     : https://prove2.me/theorems/9c0cd2cc-dfa5-4001-bd5c-c29e4d625736
-- title:
--   Finite index policies have one-sided convergent policy subsequences
-- statement:
--   Finite index vectors approaching a limiting extended-real vector from below, or strictly from above, have deterministic maximum-index policies with a subsequence converging in expected reward and cost to a limiting maximum-index policy. Equality of index vectors gives equality of the selected policies. No assumption of eventual index ranking stability is made.
-- source:
--   Auxiliary finite-table compactness and one-sided stopping-threshold lemma for the author revised Pandora Bayesian optimization manuscript.

import Definitions.Def_PandoraBO_Model
open MeasureTheory Filter
open scoped Topology
set_option autoImplicit false

theorem PandoraBO.Private20261023.finite_index_policy_subsequence_limit {n : ℕ} (M : PandoraBO.Instance n)
    (zs : ℕ → PandoraBO.Box n → EReal) (z : PandoraBO.Box n → EReal)
    (weak : Bool) (hlim : ∀ i, Tendsto (fun k => zs k i) atTop (nhds (z i)))
    (hside : ∀ i k, if weak then z i < zs k i else zs k i ≤ z i) :
    ∃ policies : ℕ → PandoraBO.Policy n,
      (∀ j k, zs j = zs k → policies j = policies k) ∧
      (∀ k, (∀ u i, zs k i ≤ zs k ((policies k).first u)) ∧
        (∀ h u, PandoraBO.validHistory h →
          match (policies k).next (h,u) with
          | none => ∀ i, ¬ PandoraBO.wasOpened h i →
              zs k i ≤ (PandoraBO.historyReward h : EReal)
          | some i => (PandoraBO.historyReward h : EReal) ≤ zs k i ∧
              ∀ j, ¬ PandoraBO.wasOpened h j → zs k j ≤ zs k i)) ∧
      ∃ extraction : ℕ → ℕ, ∃ π : PandoraBO.Policy n,
        StrictMono extraction ∧
        ((∀ u i, z i ≤ z (π.first u)) ∧
          (∀ h u, PandoraBO.validHistory h →
            match π.next (h,u) with
            | none => ∀ i, ¬ PandoraBO.wasOpened h i →
                z i ≤ (PandoraBO.historyReward h : EReal)
            | some i => (PandoraBO.historyReward h : EReal) ≤ z i ∧
                ∀ j, ¬ PandoraBO.wasOpened h j → z j ≤ z i)) ∧
        Tendsto (fun k => PandoraBO.expectedCost M (policies (extraction k))) atTop
          (nhds (PandoraBO.expectedCost M π)) ∧
        Tendsto (fun k => PandoraBO.expectedReward M (policies (extraction k))) atTop
          (nhds (PandoraBO.expectedReward M π))  := by sorry
