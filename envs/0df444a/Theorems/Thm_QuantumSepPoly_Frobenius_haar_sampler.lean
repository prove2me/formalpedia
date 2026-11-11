-- Prove2me | Theorems.Thm_QuantumSepPoly_Frobenius_haar_sampler
-- name    : QuantumSepPoly.Frobenius.haar_sampler
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:12:59.369259+00:00
-- url     : https://prove2.me/theorems/bd0652b7-9fa6-4ae5-bef1-bf8c0a247589
-- title:
--   Section 2.3 — normalized Haar sampling
-- statement:
--   The product random tape law is a probability measure. Gaussian Gram–Schmidt with positive QR phases is measurable, produces a unitary almost surely, and induces a probability measure invariant under both left and right multiplication by every unitary:
--   $$\mathcal L(VU)=\mathcal L(UV)=\mathcal L(U)=\operatorname{Haar}(U(d)).$$
--   One finite scalar program samples this distribution with charged runtime at most $C(d+1)^k$ almost surely, uniformly in dimension. Singular pivots have the defined identity output. This exposes the sampling claim in Section 2.3 as an unproved supporting target, not a free machine instruction.
--
--   Differences from the source:
--   - encoding: coordinates labelled 1 through d → coordinates indexed by Fin d from 0 through d-1; reason: canonical relabelling preserves all vectors, matrices, sums, and constraints
--   - encoding: randomized polynomial-time algorithm in exact real arithmetic → finite scalar RAM program, product random tapes, measurable output, and a charged bound C(d+1)^k preceding every input; reason: makes the source runtime and probability claims operational without changing the continuous input domain
--   - encoding: Haar probability measure and phase-normalized Gaussian QR → Gaussian-QR pushforward with explicit singular-pivot identity branch, measurable invariance, and probability-mass assertions; reason: the singular branch changes only a Gaussian null event and supplies total operational behavior
--   - generalization: positive dimension → also the zero-dimensional unitary group; reason: this group is a singleton and needs no output entries
-- source:
--   Giulio Malavolta, STOC 2027 submission #1577 (October 2026), Section 2.3, p. 8 (PDF p. 8); §§2.4,4 pp.8,13,16–17 as applicable; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1577.pdf

import Definitions.Def_QuantumSepPoly_Frobenius_FlatIO

open MeasureTheory

namespace QuantumSepPoly.Frobenius

/-- §2.3, p.8: Gaussian QR supplies the normalized Haar law, with charged
polynomial-time sampling. The singular-pivot branch is part of haarQR. -/
theorem haar_sampler : IsProbabilityMeasure tapeLaw ∧
  (∀ d : ℕ, Measurable (sampledUnitary (d := d)) ∧ IsProbabilityMeasure (haar d) ∧
    (∀ᵐ U ∂haar d, U ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
    ∀ V ∈ Matrix.unitaryGroup (Fin d) ℂ,
      (haar d).map (fun U => V*U) = haar d ∧ (haar d).map (fun U => U*V) = haar d) ∧
  ∃ (P : RAMProgram) (C : ℝ) (k : ℕ), 0 < C ∧ ∀ d : ℕ,
    (∀ᵐ tape ∂tapeLaw, RAMTerminates P (ramInitial 0 d []) (C*(d+1)^k) tape) ∧
    Measurable (fun tape (i j : Fin d) =>
      let s := ramResult P (ramInitial 0 d []) tape
      (s.real (1+2*(i.val*d+j.val)) : ℂ) + Complex.I*s.real (2+2*(i.val*d+j.val))) ∧
    tapeLaw.map (fun tape (i j : Fin d) =>
      let s := ramResult P (ramInitial 0 d []) tape
      (s.real (1+2*(i.val*d+j.val)) : ℂ) + Complex.I*s.real (2+2*(i.val*d+j.val))) = haar d := by sorry

end QuantumSepPoly.Frobenius
