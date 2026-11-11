-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_5_3
-- name    : QuantumSepPoly.Frobenius.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:13:12.154721+00:00
-- url     : https://prove2.me/theorems/1ca91c81-fd02-41f1-91c2-109b6a88a604
-- title:
--   Lemma 5.3 — Dimension-independent alphabet
-- statement:
--   Fix the positive cutoff constants and integer $m\ge2$ used in the flat decomposition. For $0<\eta<1$, $0<\delta<1/2$, Hermitian $M$ with $\|M\|_F\le1$, and unitary $U,V$ on the successful flattening event, the constructed alphabet $\Omega=E\times E$ satisfies a uniform bound
--   $$|\Omega|\le C(1+1/\eta+\log(1/\delta))^k.$$
--   Here $C>0$ and the natural exponent $k$ are fixed before dimension and matrix. This makes the alphabet size independent of both.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: absolute constants chosen for Lemma 3.3 and an alphabet of polynomial size → positive cutoff constants fixed before a uniform coefficient-degree bound for the explicitly constructed alphabet; reason: the bound is uniform in dimension and matrix, and specializes to the source chosen constants
--   - generalization: cutoff constants supplied by the moment lemma and equation (5) → any positive cutoff constants and integer m at least two; reason: the alphabet-size bound uses only these conditions; the source chosen constants are included
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 5.3, p. 20 (PDF p. 20); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_CSPReduction

namespace QuantumSepPoly.Frobenius

/-- Lemma 5.3, p.20. The polynomial is independent of dimension and input. -/
theorem lemma_5_3 (p : FlatParameters) (hc0 : 0 < p.c0) (hc1 : 0 < p.c1) (hm : 2 ≤ p.m) :
  ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ η δ : ℝ, 0 < η → η < 1 → 0 < δ → δ < 1/2 →
    ∀ (d : ℕ), 0 < d → ∀ (M : Bip d) (U V : Op d),
      M.IsHermitian → frob M ≤ 1 → U ∈ Matrix.unitaryGroup (Fin d) ℂ →
      V ∈ Matrix.unitaryGroup (Fin d) ℂ → flattenSuccess p δ (centered M) U V →
      (Fintype.card (ReductionSymbol (reductionGamma (reductionD p δ M U V)) η) : ℝ) ≤
        C*(1+1/η+Real.log (1/δ))^k := by sorry

end QuantumSepPoly.Frobenius
