-- Prove2me | Theorems.Thm_PFRelease_lemma_B_1
-- name    : PFRelease.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:46:01.902211+00:00
-- url     : https://prove2.me/theorems/c3fbb37e-4137-4c23-b28c-51099648d2f0
-- title:
--   Lemma B.1 — Boolean tests decompose as $\pi\mathbf 0+(1-\pi)\mathbf B^z$
-- statement:
--   Let $\zeta>0$ and let $\mathbf P^0,\mathbf P^1$ be distributions on $\{0,1\}$ with $\mathbf P^0\approx_{\zeta,0}\mathbf P^1$. Then there exist a weight $\pi\in[0,1]$ and distributions $\mathbf B^0,\mathbf B^1$ on $\{0,1\}$ such that, for $z\in\{0,1\}$,
--   $$
--   \mathbf P^z=\pi\,\mathbf 0+(1-\pi)\,\mathbf B^z,\qquad \mathbf B^0\approx_{\zeta,0}\mathbf B^1,\qquad \Pr[\mathbf B^z=1]\ \ge\ \underline p_\zeta:=\frac1{e^{\zeta}+1},
--   $$
--   where $\mathbf 0$ is the distribution that takes the value $0$ with probability $1$.
--
--   This decomposition turns each test of sparse vector into a mixture of a constant answer and a "private call" that fails with probability bounded below, which is what target charging counts.
--
--   Differences from the source:
--   - encoding: distributions on $\{0,1\}$ indexed by $z\in\{0,1\}$ → probability measures on `Bool` (`false` = 0, `true` = 1) indexed by `z : Bool`; reason: same objects
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Lemma B.1, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_PFRelease_Indist

open MeasureTheory

namespace PFRelease

/-- **Lemma B.1 (Boolean tests, following Lemma C.3 in [CL23])** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Lemma B.1,
p.30 = PDF p.32). Given `ζ > 0` and distributions `P₀, P₁` over `{0, 1}` with `P₀ ≈_{ζ,0} P₁`,
there exist a weight `π ∈ [0, 1]` and distributions `B₀, B₁` such that, for `z ∈ {0, 1}`,
`P_z = π·0 + (1 − π)·B_z`, `B₀ ≈_{ζ,0} B₁` and `Pr[B_z = 1] ≥ p_ζ := 1/(e^ζ + 1)`, where `0` is
the distribution that takes `0` with probability 1.

**Formalization Note** `{0, 1}` is `Bool` (`false` = 0, `true` = 1); the index `z` is a
`Bool` as well; distributions are probability measures on `Bool`, and `0` is `dirac false`. -/
theorem lemma_B_1 (ζ : ℝ) (hζ : 0 < ζ) (P : Bool → Measure Bool)
    (hP : ∀ z, IsProbabilityMeasure (P z)) (hPP : Indist (P false) (P true) ζ 0) :
    ∃ π : ℝ, 0 ≤ π ∧ π ≤ 1 ∧ ∃ B : Bool → Measure Bool, (∀ z, IsProbabilityMeasure (B z)) ∧
      (∀ z, P z = ENNReal.ofReal π • Measure.dirac false + ENNReal.ofReal (1 - π) • B z) ∧
      Indist (B false) (B true) ζ 0 ∧
      ∀ z, ENNReal.ofReal (1 / (Real.exp ζ + 1)) ≤ B z {true} := by sorry

end PFRelease
