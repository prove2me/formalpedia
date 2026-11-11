-- Prove2me | Theorems.Thm_TestableSanitization_Robust_isolation_soundness
-- name    : TestableSanitization.Robust.isolation_soundness
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:53:39.944484+00:00
-- url     : https://prove2.me/theorems/74d44fc6-d864-41d2-a19c-06d973103c31
-- title:
--   §4.1, proof of Theorem 8, "Soundness of the isolation test" — if $\mathrm{Iso}_{D,L}(f,b)>3a/2$ the test passes ($\hat I\le a$) with probability at most $\zeta/4$
-- statement:
--   Let $d\ge1$, $L>0$, $b\in(0,1]$, $a,\zeta\in(0,1/2)$, $D$ a probability distribution on $\mathbb R^d$ and $f$ a measurable classifier. Run the isolation test of Algorithm 3 with $m=\lceil\frac{50}a\log\frac8\zeta\rceil$ points and $K=\lceil\frac{12}b\log\frac{8m}\zeta\rceil$ perturbations per point: draw $x_1,\dots,x_m$ i.i.d. from $D$ and, independently, $Z_{ij}$ i.i.d. uniform on the unit ball; set $\tilde\phi_i=\frac1K\sum_j\mathbb 1\{f(x_i+LZ_{ij})\neq f(x_i)\}$ and $\hat I=\frac1m\sum_i\mathbb 1\{\tilde\phi_i>b/2\}$. If $\mathrm{Iso}_{D,L}(f,b)>3a/2$, then
--   $$\Pr[\hat I\le a]\le\zeta/4 .$$
--   Equivalently: except with probability at most $\zeta/4$, passing the isolation test implies $\mathrm{Iso}_{D,L}(f,b)\le3a/2$.
--
--   Combined with Eq. (5), this is the soundness half of Theorem 1: an accepted function has small isolation, hence a sanitized output with small boundary and small honest loss.
--
--   Differences from the source:
--   - generalization: b as in (1), i.e. b = (s/L)^d/32 for L > r > 0 → any b ∈ (0, 1] and any L > 0; reason: the argument uses only 0 < b ≤ 1 and L > 0; the b of (1) lies in (0, 1/32], so the Lean statement specializes to the paper's
--   - generalization: D a probability distribution with E_{x∼D}‖x‖ ≤ µ (Theorem 8's standing assumption) → any probability measure D on R^d; reason: the moment bound is not used by the isolation test's analysis; the paper's D is an instance
--   - encoding: the input space R^d (a dimension, d ≥ 1 as in Lemma 34) → d : ℕ with the hypothesis 1 ≤ d, points in EuclideanSpace ℝ (Fin d); reason: Lean convention for R^d with the Euclidean norm; excludes only the degenerate d = 0
--   - encoding: a Borel-measurable classifier f : R^d → {±1} (§2 standing assumption) → f : Pt d → ℝ with IsClassifier f (Measurable f and every value is 1 or -1); reason: the two labels ±1 as reals; same functions
--   - encoding: x_1, …, x_m i.i.d. from D and Z_ij i.i.d. from U, independent; ϕ̃_i and Î of Algorithm 3; m, K as in (4); a, ζ ∈ (0, 1/2) → the product law isoLaw D m K, phiTilde and isoStat, m = mParam a ζ, K = KParam b m ζ (natural ceilings), hypotheses 0 < a < 1/2, 0 < ζ < 1/2; reason: the definitions of Algorithm 3 and (4)
--   - encoding: 'except with probability at most ζ/4, passing the isolation test implies Iso_{D,L}(f, b) ≤ 3a/2' → Iso_{D,L}(f, b) > 3a/2 implies isoLaw{Î ≤ a} ≤ ζ/4; reason: Iso_{D,L}(f, b) is deterministic, so the two forms say the same thing
--   - encoding: probabilities and expectations as real numbers → measures of sets and lower Lebesgue integrals in [0, ∞] (ENNReal), compared with ENNReal.ofReal of the real bounds; reason: the values lie in [0, 1]; ENNReal avoids integrability side conditions, and the measure of a possibly non-measurable set is its outer measure, which can only make an upper bound stronger
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 26 (PDF 28), §4.1, proof of Theorem 8, paragraph "Soundness of the isolation test"

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Boundary
import Definitions.Def_TestableSanitization_Robust_Params

open MeasureTheory

namespace TestableSanitization.Robust

theorem isolation_soundness (d : ℕ) (hd : 1 ≤ d) (L b a ζ : ℝ) (hL : 0 < L) (hb : 0 < b)
    (hb' : b ≤ 1) (ha : 0 < a) (ha' : a < 1 / 2) (hζ : 0 < ζ) (hζ' : ζ < 1 / 2)
    (D : Measure (Pt d)) [IsProbabilityMeasure D] (f : Pt d → ℝ) (hf : IsClassifier f)
    (hIso : ENNReal.ofReal (3 * a / 2) < Iso D L f b) :
    isoLaw D (mParam a ζ) (KParam b (mParam a ζ) ζ)
        {ω | isoStat f L b (mParam a ζ) (KParam b (mParam a ζ) ζ) ω ≤ a} ≤
      ENNReal.ofReal (ζ / 4) := by sorry

end TestableSanitization.Robust
