-- Prove2me | Theorems.Thm_PRUPermLayer_fact_2_5
-- name    : PRUPermLayer.fact_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:33.238796+00:00
-- url     : https://prove2.me/theorems/94eca299-7f20-4b9e-ad36-1613e8a26a18
-- title:
--   Fact 2.5 — quantum union bounds (factor 4 in general, 1 for commuting projectors)
-- statement:
--   Let $\rho$ be a density operator and $\Pi_1, \dots, \Pi_m$ orthogonal projectors. Then
--   $$
--   1 - \mathrm{Tr}(\Pi_m \cdots \Pi_1\,\rho\,\Pi_1\cdots\Pi_m) \le 4\sum_{i=1}^m \mathrm{Tr}\big((I - \Pi_i)\rho\big).
--   $$
--   If the projectors commute, the factor $4$ can be removed.
--
--   The general bound is Gao's [Gao15]; the commuting one is [FLM+26, Lemma 7.4], [OV22]. Both clauses are stated.
--
--   Differences from the source:
--   - encoding: $\mathrm{Tr}(\cdot)$ of positive operators (real) → real parts of the traces; reason: the traces are real; same inequality
--   - encoding: projectors $\Pi_1,\dots,\Pi_m$ → $P_0,\dots,P_{m-1}$, Hermitian idempotents, with $\Pi_1$ acting first; reason: Lean indexing; same statement
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Fact 2.5, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Fact 2.5** (quantum union bounds; Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Fact 2.5, p.11 (PDF p.13), citing [Gao15] and
[FLM+26, Lemma 7.4], [OV22]). Let `ρ` be a density operator and `Π₁, …, Π_m` orthogonal
projectors. Then `1 − Tr(Π_m ⋯ Π₁ ρ Π₁ ⋯ Π_m) ≤ 4 Σᵢ Tr((I − Πᵢ)ρ)`, and if the projectors
commute the factor `4` can be removed.

**Formalization Note** `P i` is the source's `Π_{i+1}`. `Π_m ⋯ Π₁` is
`(List.ofFn P).reverse.prod` (so `Π₁` acts first on `ρ`) and `Π₁ ⋯ Π_m` is `(List.ofFn P).prod`.
"Orthogonal projector" is a Hermitian idempotent. The traces are real; their real parts are
compared. -/
theorem fact_2_5 {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ)
    (hρ : QAlgorithms.IsDensityMatrix ρ) (m : ℕ) (P : Fin m → Matrix ι ι ℂ)
    (hP : ∀ i, (P i).IsHermitian ∧ P i * P i = P i) :
    1 - ((List.ofFn P).reverse.prod * ρ * (List.ofFn P).prod).trace.re ≤
        4 * ∑ i, ((1 - P i) * ρ).trace.re ∧
      ((∀ i j, P i * P j = P j * P i) →
        1 - ((List.ofFn P).reverse.prod * ρ * (List.ofFn P).prod).trace.re ≤
          ∑ i, ((1 - P i) * ρ).trace.re) := by sorry

end PRUPermLayer
