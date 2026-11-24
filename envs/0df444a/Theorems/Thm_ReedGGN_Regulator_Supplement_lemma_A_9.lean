-- Prove2me | Theorems.Thm_ReedGGN_Regulator_Supplement_lemma_A_9
-- name    : ReedGGN.Regulator.Supplement.lemma_A_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T05:13:23.721941+00:00
-- url     : https://prove2.me/theorems/f89e567f-a9f9-4cc7-85a8-6b07b8cb8315
-- title:
--   Lemma A.9 (corrected: convolution sign)
-- statement:
--   Let $F$ be the fixed nonnegative mean-one service CDF with tail $G$. For arbitrary càdlàg path coordinates, set
--
--   $$f(q,w,a,m)=(q,w,K_G^{\rm inc}a,m),\qquad K_G^{\rm inc}a(t)=G(0)a(t)-G(t)a(0)-\int_{(0,t]}a(t-s)dF(s).$$
--
--   The entire map $f$ preserves the càdlàg domain and is measurable for $\mathcal B(\mathbb R)\otimes\mathcal D^3$. It is continuous for the maximum product J₁ topology at every point whose three path coordinates are continuous. Continuity is expressed by preservation of every convergent sequence at each such point, which is equivalent in this metric space.
--
--   This is a deterministic mapping result on the whole domain; it has no arrival FCLT or initial-law hypothesis. The integration-by-parts sign is corrected, and the erroneous proof-internal constant on p.58 is not asserted.
--
--   Differences from the source:
--   - encoding: weak convergence in the maximum product J₁ metric on nonnegative-time càdlàg paths → full path-law coupling with scalar J₁ time changes separately for each path coordinate; N=n+1; reason: Skorohod representation on the Polish path space gives the same weak convergence, including discontinuous limits; indexing never divides by zero
--   - correction: (A.69) writes G(0)x(t)−G(t)x(0)−∫x(t−s)dG(s) → increment convolution G(0)x(t)−G(t)x(0)−∫_(0,t]x(t−s)dF(s); reason: dG=−dF; for F the unit mass at 1 and x(t)=t, the printed expression gives 3 at t=2 instead of the integral value 1; (A.68), (5.19) and the verified boundary example identify the sign
--   - encoding: continuity of the full map at every continuous-coordinate limit point → preservation of all product-J₁ convergent sequences, together with full-map measurability and preservation of the càdlàg locus; reason: the product space is metrizable, so sequential continuity is equivalent to continuity; no proof-internal Lipschitz constant is asserted
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, Lemma A.9, p.56

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_Drivers

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

namespace ReedGGN.Regulator.Supplement

theorem lemma_A_9 (μ : Measure ℝ) (hμ : ServiceLaw μ) :
    (∀ x : State 3, Admissible x → Admissible (convolutionMap μ x)) ∧
    Measurable (fun x : {x : State 3 // Admissible x} => convolutionMap μ x.val) ∧
    ∀ (x : State 3), (∀ i, Continuous (x.2 i)) →
      ∀ xs : ℕ → State 3, ProductJ1 xs x →
        ProductJ1 (fun n => convolutionMap μ (xs n)) (convolutionMap μ x) := by sorry

end ReedGGN.Regulator.Supplement
