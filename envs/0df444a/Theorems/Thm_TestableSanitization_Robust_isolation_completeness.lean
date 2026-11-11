-- Prove2me | Theorems.Thm_TestableSanitization_Robust_isolation_completeness
-- name    : TestableSanitization.Robust.isolation_completeness
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:53:34.871686+00:00
-- url     : https://prove2.me/theorems/9d8b93fd-aa18-459d-854a-cf1b88221e3f
-- title:
--   §4.1, proof of Theorem 8, "Completeness of the isolation test" — if $\mathrm{NS}_{D,L}(f)\le2ab/5$ or $\mathrm{Iso}_{D,L}(f,b/4)\le a/2$, then $\Pr[\hat I>a]\le\zeta/4$
-- statement:
--   Let $d\ge1$, $L>0$, $b\in(0,1]$, $a,\zeta\in(0,1/2)$, $D$ a probability distribution on $\mathbb R^d$ and $f$ a measurable classifier, and run the isolation test of Algorithm 3 with $m=\lceil\frac{50}a\log\frac8\zeta\rceil$ and $K=\lceil\frac{12}b\log\frac{8m}\zeta\rceil$ (i.i.d. points $x_i\sim D$, independent i.i.d. perturbations $Z_{ij}\sim U$, $\tilde\phi_i=\frac1K\sum_j\mathbb 1\{f(x_i+LZ_{ij})\neq f(x_i)\}$, $\hat I=\frac1m\sum_i\mathbb 1\{\tilde\phi_i>b/2\}$). If
--   $$\mathrm{NS}_{D,L}(f)\le\frac{2ab}5\quad\text{or}\quad\mathrm{Iso}_{D,L}(f,b/4)\le\frac a2,$$
--   then $\Pr[\hat I>a]\le\zeta/4$: the isolation test passes except with probability at most $\zeta/4$.
--
--   With Lemma 12 this gives the completeness half of Theorem 1: a robust function has small isolation at the testing radius and is accepted with high probability.
--
--   Differences from the source:
--   - generalization: b as in (1), i.e. b = (s/L)^d/32 for L > r > 0 → any b ∈ (0, 1] and any L > 0; reason: the argument uses only 0 < b ≤ 1 and L > 0; the b of (1) lies in (0, 1/32], so the Lean statement specializes to the paper's
--   - generalization: D a probability distribution with E_{x∼D}‖x‖ ≤ µ (Theorem 8's standing assumption) → any probability measure D on R^d; reason: the moment bound is not used by the isolation test's analysis; the paper's D is an instance
--   - encoding: the input space R^d (a dimension, d ≥ 1 as in Lemma 34) → d : ℕ with the hypothesis 1 ≤ d, points in EuclideanSpace ℝ (Fin d); reason: Lean convention for R^d with the Euclidean norm; excludes only the degenerate d = 0
--   - encoding: a Borel-measurable classifier f : R^d → {±1} (§2 standing assumption) → f : Pt d → ℝ with IsClassifier f (Measurable f and every value is 1 or -1); reason: the two labels ±1 as reals; same functions
--   - encoding: x_1, …, x_m i.i.d. from D and Z_ij i.i.d. from U, independent; ϕ̃_i and Î of Algorithm 3; m, K as in (4); a, ζ ∈ (0, 1/2) → the product law isoLaw D m K, phiTilde and isoStat, m = mParam a ζ, K = KParam b m ζ (natural ceilings), hypotheses 0 < a < 1/2, 0 < ζ < 1/2; reason: the definitions of Algorithm 3 and (4)
--   - encoding: 'the isolation test passes … the total failure probability is at most ζ/8 + ζ/8 = ζ/4' → isoLaw{a < Î} ≤ ζ/4; reason: the test fails exactly when Î > a (Algorithm 3)
--   - encoding: probabilities and expectations as real numbers → measures of sets and lower Lebesgue integrals in [0, ∞] (ENNReal), compared with ENNReal.ofReal of the real bounds; reason: the values lie in [0, 1]; ENNReal avoids integrability side conditions, and the measure of a possibly non-measurable set is its outer measure, which can only make an upper bound stronger
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 26 (PDF 28), §4.1, proof of Theorem 8, paragraph "Completeness of the isolation test"

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Boundary
import Definitions.Def_TestableSanitization_Robust_Params

open MeasureTheory

namespace TestableSanitization.Robust

theorem isolation_completeness (d : ℕ) (hd : 1 ≤ d) (L b a ζ : ℝ) (hL : 0 < L) (hb : 0 < b)
    (hb' : b ≤ 1) (ha : 0 < a) (ha' : a < 1 / 2) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2)
    (D : Measure (Pt d)) [IsProbabilityMeasure D] (f : Pt d → ℝ) (hf : IsClassifier f)
    (hfa : NS D L f ≤ ENNReal.ofReal (2 * a * b / 5) ∨ Iso D L f (b / 4) ≤ ENNReal.ofReal (a / 2)) :
    isoLaw D (mParam a ζ) (KParam b (mParam a ζ) ζ)
        {ω | a < isoStat f L b (mParam a ζ) (KParam b (mParam a ζ) ζ) ω} ≤
      ENNReal.ofReal (ζ / 4) := by sorry

end TestableSanitization.Robust
