-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_proposition_3_2
-- name    : QuantumSepPoly.Frobenius.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:55.78636+00:00
-- url     : https://prove2.me/theorems/5cc40f92-f9df-418d-8dc6-85ad6e8ea4cc
-- title:
--   Proposition 3.2 — Locally rotated entry moments
-- statement:
--   There are absolute $c_0,c_1>0$ such that every complex bipartite operator $M$ with both partial traces zero, independent Haar unitaries $U,V$, and integer $1\le p\le c_0d$ satisfy, at each entry,
--   $$\|[(U\otimes V)^*M(U\otimes V)]_{ac,be}\|_{L^{2p}}\le c_1p^2\|M\|_F/d^2.$$
--   No Hermitian restriction is imposed. This records the scale of each locally rotated entry.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: independent Haar unitaries and finite L^(2p) magnitude → product Haar law and extended-real nonnegative moment; reason: identical independence and norm scale with no integrability default
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Proposition 3.2, p. 11 (PDF p. 11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_HaarQR

namespace QuantumSepPoly.Frobenius

/-- Proposition 3.2, p.11. There is no Hermitian restriction. -/
theorem proposition_3_2 : ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧
  ∀ (d : ℕ) (M : Bip d), trace0 M = 0 → trace1 M = 0 →
  ∀ (a b c e : Fin d) (p : ℕ), 1 ≤ p → (p : ℝ) ≤ c0*d →
    Lq ((haar d).prod (haar d)) (2*p)
      (fun UV => ‖locallyRotate M UV.1 UV.2 (a,c) (b,e)‖) ≤
        ENNReal.ofReal (c1 * (p : ℝ)^2 / (d : ℝ)^2 * frob M) := by sorry

end QuantumSepPoly.Frobenius
