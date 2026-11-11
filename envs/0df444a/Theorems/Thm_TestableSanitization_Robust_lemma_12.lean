-- Prove2me | Theorems.Thm_TestableSanitization_Robust_lemma_12
-- name    : TestableSanitization.Robust.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:52:50.326183+00:00
-- url     : https://prove2.me/theorems/c5905524-418e-4992-9fb7-3ed28098f09d
-- title:
--   Lemma 12 — $\mathrm{NS}_{D,\delta}(f)\le D(\partial f_\delta)$ and $\mathrm{Iso}_{D,\delta}(f,b)\le\Pr_{x\sim D}[\phi_{f,\delta}(x)>0]\le D(\partial f_\delta)$
-- statement:
--   Let $d\ge1$, $D$ a probability distribution on $\mathbb R^d$ and $f$ a measurable classifier. For every $\delta>0$ and $b\in(0,1)$,
--   $$\mathrm{NS}_{D,\delta}(f)\le D(\partial f_\delta),\qquad \mathrm{Iso}_{D,\delta}(f,b)\le\Pr_{x\sim D}[\phi_{f,\delta}(x)>0]\le D(\partial f_\delta).$$
--
--   The lemma translates the robustness assumption of completeness ($D(\partial f_{\alpha r})\le c\eta$) into the small noise sensitivity and isolation that the isolation test detects.
--
--   Differences from the source:
--   - encoding: the input space R^d (a dimension, d ≥ 1 as in Lemma 34) → d : ℕ with the hypothesis 1 ≤ d, points in EuclideanSpace ℝ (Fin d); reason: Lean convention for R^d with the Euclidean norm; excludes only the degenerate d = 0
--   - encoding: a Borel-measurable classifier f : R^d → {±1} (§2 standing assumption) → f : Pt d → ℝ with IsClassifier f (Measurable f and every value is 1 or -1); reason: the two labels ±1 as reals; same functions
--   - encoding: probabilities and expectations as real numbers → measures of sets and lower Lebesgue integrals in [0, ∞] (ENNReal), compared with ENNReal.ofReal of the real bounds; reason: the values lie in [0, 1]; ENNReal avoids integrability side conditions, and the measure of a possibly non-measurable set is its outer measure, which can only make an upper bound stronger
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 27 (PDF 29), Lemma 12

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Boundary

open MeasureTheory

namespace TestableSanitization.Robust

theorem lemma_12 (d : ℕ) (hd : 1 ≤ d) (D : Measure (Pt d)) [IsProbabilityMeasure D]
    (f : Pt d → ℝ) (hf : IsClassifier f) (δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b) (hb' : b < 1) :
    NS D δ f ≤ boundaryMass D δ f ∧
      Iso D δ f b ≤ D {x | 0 < lns f δ x} ∧
      D {x | 0 < lns f δ x} ≤ boundaryMass D δ f := by sorry

end TestableSanitization.Robust
