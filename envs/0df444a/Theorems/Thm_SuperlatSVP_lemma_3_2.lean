-- Prove2me | Theorems.Thm_SuperlatSVP_lemma_3_2
-- name    : SuperlatSVP.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:45:06.50927+00:00
-- url     : https://prove2.me/theorems/952ed1cc-71e0-4a8c-ae1d-95aca3939fd6
-- title:
--   Lemma 3.2 — $\rho_s(kL\setminus\{0\})\le\frac1k\rho_s(L\setminus\{0\})$
-- statement:
--   For every full-rank lattice $L=B\mathbb Z^n$, every $s>0$ and every integer $k\ge1$,
--   $$\rho_s(kL\setminus\{0\})\le\frac1k\,\rho_s(L\setminus\{0\}),$$
--   where $kL=\{kv:v\in L\}$ and $\rho_s(S)=\sum_{x\in S}e^{-\pi\|x\|^2/s^2}$.
--
--   Scaling a lattice by $k$ thins its nonzero Gaussian mass by at least the factor $k$. Applied to $pL^*$, this gives Lemma 3.1.
--
--   Differences from the source:
--   - encoding: Gaussian masses as real sums → sums of nonnegative terms in [0,∞]; reason: Lean convention; the sums are finite for lattices, so no instance changes
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §3, p.24 (PDF p.24), Lemma 3.2, eq. (3.4)

import Mathlib
import Definitions.Def_SuperlatSVP_lat

open MeasureTheory Filter
open scoped ENNReal

namespace SuperlatSVP

/-- Lemma 3.2 (Non-zero Gaussian masses of scaled lattices). Hhan, Kim, Kim, Laarhoven, *Superlattice methods for the shortest vector problem and discrete
Gaussian sampling*, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §3, p.24 (PDF p.24): "For every
lattice L, parameter s > 0, and integer k ≥ 1, ρs(kL ∖ {0}) ≤ (1/k) ρs(L ∖ {0}). (3.4)"

**Formalization Note.** Lattices are full rank (§2.1, p.14: "All lattices considered here have full
rank"). `kL = {k v : v ∈ L}`. Masses in `ℝ≥0∞`. -/
theorem lemma_3_2 (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (hk : 1 ≤ k) :
    rhoSet s ({x : E n | ∃ v ∈ lat B, x = (k : ℝ) • v} \ {0}) ≤
      (k : ℝ≥0∞)⁻¹ * rhoSet s ((lat B : Set (E n)) \ {0}) := by sorry

end SuperlatSVP
