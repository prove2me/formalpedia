-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P26_histories_normalization
-- name    : QAlgorithms.Papers.Independent.Dependency50.P26.histories_normalization
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:48:24.113375+00:00
-- url     : https://prove2.me/theorems/0246e792-a16a-4431-a983-bd6086917922
-- title:
--   §VI question 2: admissible sets of histories
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces of positive dimension with fixed orthonormal bases. Let $N,k\ge1$ and let a finite family of multipartite Kraus histories define $R_i=\sum_a|K_{ia}\rangle\rangle\langle\langle K_{ia}|$. Such a family is a generalized measurement exactly when its total satisfies all deterministic comb normalizations:
--
--   $$
--   \{R_i\}_{i=1}^k\text{ is an }N\text{-instrument}\quad\Longleftrightarrow\quad\sum_iR_i\text{ satisfies Eq.(25)}.
--   $$
--
--   The positivity of each branch follows from its Kraus expression. No earlier normalization equation is omitted.
-- source:
--   Theoretical framework for quantum networks, arXiv:0904.4483v2, PDF p. 21, §VI question 2: admissible sets of histories

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P26

/-- PDF p.21, question 2: Kraus histories form a measurement exactly when their total
satisfies all causal normalization constraints, not merely its final trace equation. -/
theorem histories_normalization (s : Signature) (n k q : ℕ)
    (hn : 0 < n) (hk : 0 < k) (K : Fin k → Fin q → Basis s n → ℂ) :
    CombInstrument s n k (fun i => ∑ a, rankOne (K i a)) ↔
      Normalized s n (∑ i, ∑ a, rankOne (K i a)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P26

end
