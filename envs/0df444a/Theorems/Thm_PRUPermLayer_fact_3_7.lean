-- Prove2me | Theorems.Thm_PRUPermLayer_fact_3_7
-- name    : PRUPermLayer.fact_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:21.903756+00:00
-- url     : https://prove2.me/theorems/1dbc485b-f89b-4214-9ab2-0f5b7488c1c9
-- title:
--   Fact 3.7 — $\|\mathrm{Tr}_T\rho_{ST} - \mathrm{Tr}_T(\Pi_T\rho_{ST}\Pi_T)\|_1 = 1 - \mathrm{Tr}(\Pi_T\rho_{ST})$
-- statement:
--   For a density operator $\rho_{ST}$ on registers $S$ and $T$ and a projector $\Pi_T$ on $T$,
--   $$
--   \big\|\mathrm{Tr}_T\,\rho_{ST} - \mathrm{Tr}_T(\Pi_T\,\rho_{ST}\,\Pi_T)\big\|_1 = 1 - \mathrm{Tr}(\Pi_T\,\rho_{ST}),
--   $$
--   where $\Pi_T$ acts as $\Pi_T \otimes I$ and $\|\cdot\|_1$ is the trace norm.
--
--   The paper imports this from [FLM+26, Lemma 6.1] and [MH25]. Projecting a register that is discarded afterwards costs exactly the probability of failing the projection, with no square root.
--
--   Differences from the source:
--   - encoding: $\rho_{ST}$ with $T$ second → $\rho$ on $T \times S$ ($T$ first); reason: so that the published partial trace over the first factor traces out $T$; same statement
--   - encoding: $\mathrm{Tr}(\Pi_T\rho_{ST})$ → its real part; reason: the trace is real
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Fact 3.7, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
open MeasureTheory
open scoped ComplexOrder Matrix

namespace PRUPermLayer

/-- **Fact 3.7** (Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), Fact 3.7, p.14 (PDF p.16), quoting [FLM+26, Lemma 6.1] and [MH25]). For a
density operator `ρ_{ST}` and a projector `Π_T` on `T`,
`‖Tr_T ρ_{ST} − Tr_T(Π_T ρ_{ST} Π_T)‖₁ = 1 − Tr(Π_T ρ_{ST})`.

**Formalization Note** The register `T` is the first tensor factor (`ρ` on `T × S`), so that the
published `QAlgorithms.traceLeft` traces it out; `Π_T` acts as `Π_T ⊗ I`. `‖·‖₁` is the published
`QAlgorithms.traceNorm`. The trace `Tr(Π_T ρ)` is real; its real part is written. -/
theorem fact_3_7 {T S : Type*} [Fintype T] [DecidableEq T] [Fintype S] [DecidableEq S]
    (ρ : Matrix (T × S) (T × S) ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) (P : Matrix T T ℂ)
    (hP : P.IsHermitian ∧ P * P = P) :
    QAlgorithms.traceNorm (QAlgorithms.traceLeft ρ -
        QAlgorithms.traceLeft (Matrix.kroneckerMap (· * ·) P (1 : Matrix S S ℂ) * ρ *
          Matrix.kroneckerMap (· * ·) P (1 : Matrix S S ℂ))) =
      1 - (Matrix.kroneckerMap (· * ·) P (1 : Matrix S S ℂ) * ρ).trace.re := by sorry

end PRUPermLayer
