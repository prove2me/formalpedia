-- Prove2me | Theorems.Thm_QTolTest1673_Unified_Supplement_lemma_8_1
-- name    : QTolTest1673.Unified.Supplement.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T13:26:25.127065+00:00
-- url     : https://prove2.me/theorems/9c426dfa-53e8-4ac8-aa2a-9574cd3e5028
-- title:
--   Lemma 8.1 — YES distance
-- statement:
--   YES distance: for every public encoding ρ and hidden string h, the function f_y built from the YES table y_i = G(h|ρ_i) has corr(f_y, J_k) ≥ 1/4 and dist(f_y, J_{n0,k}) ≤ 3/8.
--
--   $$\operatorname{corr}(f_y,J_{n_0,k})\ge\tfrac14,\qquad\operatorname{dist}(f_y,J_{n_0,k})\le\tfrac38.$$
--
--   This result supplies a supporting statement for Theorem 8.5.
--
--   Differences from the source:
--   - encoding: sign-valued functions on one-based binary coordinates → bit-valued functions on Fin-indexed binary coordinates, with sign (-1)^bit; reason: the published models give a bijective representation and preserve the value oracle and uniform Hamming distance
--   - generalization: the prescribed address shifts b_z=(z_1,z_2,z_3) and sufficiently large k in Section 8.1 → arbitrary public three-bit shifts at every k admitting an injection-valued encoding; reason: each surviving YES coefficient has magnitude at least 1/4 for every shift; existence of the encoding forces K≥6 and a+K=k, which are the only size properties used; all source instances specialize directly
--   - encoding: n₀=2K+a input variables in the Section 8 construction → a+2K coordinates ordered as address bits followed by data pairs; reason: this is a coordinate relabelling; existence of the injection-valued encoding implies K≥6 and hence a+K=k, without an extra hypothesis
-- source:
--   Zekun Ye, Jialin Zhang, Quantum Tolerant Testing of Fourier Dimensionality and Juntas, STOC 2027 submission #1673 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1673.pdf, SHA-256 5f8e9058de57e5bfe86cd485966905d576e77df38d613213662f8930b3e0e51e, Lemma 8.1, p. 34

import Mathlib
import Definitions.Def_QTolTest1673_Unified_Supplement_Rows

open scoped BigOperators
open Classical QAlgorithms FourierDimTesting102.Quantum
open Filter MeasureTheory

namespace QTolTest1673.Unified.Supplement

/-- Lemma 8.1, p.34. Every encoding, hidden string, and shifts as in (11). -/
theorem lemma_8_1 (k : ℕ)
    (ρ : Encoding (a8 k) (K8 k)) (shifts : V (a8 k) → V 3) (h : V (K8 k)) :
  1/4 ≤ corrToSet (rowFn ρ shifts (yesTable ρ h)) (junta (n8 k) k) ∧
    distToSet (rowFn ρ shifts (yesTable ρ h)) (junta (n8 k) k) ≤ 3/8 := by sorry

end QTolTest1673.Unified.Supplement
