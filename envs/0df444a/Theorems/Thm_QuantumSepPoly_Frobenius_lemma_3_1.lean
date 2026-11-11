-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_lemma_3_1
-- name    : QuantumSepPoly.Frobenius.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:11:04.326812+00:00
-- url     : https://prove2.me/theorems/cfb024dd-7526-40e1-b077-391198edce26
-- title:
--   Lemma 3.1 — Haar linear-map moment bound
-- statement:
--   There are absolute constants $c_0,c_1>0$, independent of the dimension, finite-dimensional complex Hilbert space $H$, and complex-linear map $A:\mathcal L(\mathbb C^d)\to H$, such that, for every $a,b$ and every real $2\le q\le c_0d$,
--   $$\|A(UH_{ab}U^*)\|_{L^q(H)}\le c_1(q/d)\|A\|_F,$$
--   where $U$ has normalized Haar law, $H_{ab}=u_bu_a^*-\delta_{ab}I/d$, and the map norm is Hilbert–Schmidt. This is the uniform linear-map moment estimate.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: uniform Haar unitary and Hilbert-Schmidt map norm → Gaussian-QR pushforward law and sum of squared images of matrix units; reason: the separate sampler target certifies normalized Haar invariance; the matrix units are a Frobenius orthonormal basis
--   - encoding: finite Hilbert-valued Lq moment → extended-real nonnegative moment of the Hilbert norm; reason: the finite right-hand side enforces moment finiteness without a Bochner default
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Lemma 3.1, p. 9 (PDF p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_HaarQR

namespace QuantumSepPoly.Frobenius

/-- Lemma 3.1, p.9. Absolute constants precede every dimension and linear map. -/
theorem lemma_3_1 : ∃ c0 c1 : ℝ, 0 < c0 ∧ 0 < c1 ∧
  ∀ (d : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (A : Op d →ₗ[ℂ] H) (a b : Fin d) (q : ℝ),
    2 ≤ q → q ≤ c0*d →
    Lq (haar d) q (fun U => ‖A (U * Hentry d a b * U.conjTranspose)‖) ≤
      ENNReal.ofReal (c1 * (q/d) * linearFrob A) := by sorry

end QuantumSepPoly.Frobenius
