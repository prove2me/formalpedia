-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_3_3
-- name    : QuantumSepPoly.Frobenius.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:40.2841+00:00
-- url     : https://prove2.me/theorems/cf90a06b-2923-4a84-bf24-c5d4b4c75f34
-- title:
--   Lemma 3.3 — Computable flat/tail decomposition
-- statement:
--   There is an absolute $c_{\rm flat}>0$ and a computable threshold construction such that, for every Hermitian $M$ with zero partial traces and $0<\delta<1/2$, independent Haar $U,V$ give, with probability at least $1-\delta^2$, Hermitian parts satisfying
--   $$(U\otimes V)^*M(U\otimes V)=M_{\rm flat}+M_{\rm tail},\quad\|M_{\rm tail}\|_F\le\delta\|M\|_F,$$
--   $$\|M_{\rm flat}\|_{\max}\le c_{\rm flat}(1+\log(1/\delta))^2\|M\|_F/d^2.$$
--   For each fixed accuracy, an actual finite program computes these parts in a number of charged operations polynomial in dimension. This supplies the flat object used in the reduction.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: randomized polynomial-time algorithm in exact real arithmetic → finite scalar RAM program, product random tapes, measurable output, and a charged bound C(d+1)^k preceding every input; reason: makes the source runtime and probability claims operational without changing the continuous input domain
--   - encoding: integer p satisfying (6) and branchwise absolute flat constants → p is the ceiling of m(1+log(1/delta)) and a single common dominating flat constant; reason: the ceiling lies in the stated interval; the two branch constants can share an absolute upper bound
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 3.3, p. 12 (PDF p. 12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_FlatIO

open MeasureTheory

namespace QuantumSepPoly.Frobenius

/-- Lemma 3.3, pp.12–13. The decomposition is the computed threshold decomposition.
Its finite program, charged runtime, and high-probability guarantee are all conclusions. -/
theorem lemma_3_3 : ∃ (p : FlatParameters) (cflat : ℝ),
  0 < p.c0 ∧ 0 < p.c1 ∧ 2 ≤ p.m ∧ 0 < cflat ∧
  64*p.c1^2 * ((p.m:ℝ)+1)^4 * (8:ℝ)^(-(2*(p.m:ℤ))) ≤ 1/2 ∧
  ∀ (δ : ℝ), 0 < δ → δ < 1/2 →
    (∃ (P : RAMProgram) (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (d : ℕ), 0 < d → ∀ (M : Bip d) (U V : Op d),
        M.IsHermitian → trace0 M = 0 → trace1 M = 0 →
        U ∈ Matrix.unitaryGroup (Fin d) ℂ → V ∈ Matrix.unitaryGroup (Fin d) ℂ →
        ∀ tape, RAMTerminates P (flatInitial δ M U V) (C*(d+1)^k) tape ∧
          matrixOutput d 0 (ramResult P (flatInitial δ M U V) tape) = flatPart p δ M U V ∧
          matrixOutput d (2*d^4) (ramResult P (flatInitial δ M U V) tape) = tailPart p δ M U V) ∧
    ∀ (d : ℕ), 0 < d → ∀ (M : Bip d), M.IsHermitian → trace0 M = 0 → trace1 M = 0 →
      ((haar d).prod (haar d)) {UV |
        (flatPart p δ M UV.1 UV.2).IsHermitian ∧ (tailPart p δ M UV.1 UV.2).IsHermitian ∧
        locallyRotate M UV.1 UV.2 = flatPart p δ M UV.1 UV.2 + tailPart p δ M UV.1 UV.2 ∧
        frob (tailPart p δ M UV.1 UV.2) ≤ δ*frob M ∧
        maxEntry (flatPart p δ M UV.1 UV.2) ≤
          cflat * (1+Real.log (1/δ))^2 * frob M / (d:ℝ)^2} ≥ ENNReal.ofReal (1-δ^2) := by sorry

end QuantumSepPoly.Frobenius
