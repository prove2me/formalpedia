-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P30_symmetric_classical_sampling
-- name    : QAlgorithms.Papers.Independent.Advance50.P30.symmetric_classical_sampling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:00:27.338086+00:00
-- url     : https://prove2.me/theorems/dda08f9e-8358-44f1-a8a9-eb184bfbe68c
-- title:
--   Proposition 1: cited full-sample versus subsample frequency bound
-- statement:
--   Let $p$ be a normalized nonnegative probability mass function on strings of length $n+k$ over an alphabet of size $w\ge1$, invariant under all permutations. Let $k\ge1$, $n\ge0$, and let $Q$ and $Q_{\mathrm{sample}}$ be the empirical frequencies of the whole string and its last $k$ coordinates, respectively, under this same joint law. For every $\epsilon\ge0$, $$\Pr_p\{\|Q-Q_{\mathrm{sample}}\|_1\ge\epsilon\}\le w\exp[-k\epsilon^2/(8w)].$$ The norm is full L1; the subsample is not drawn independently of the whole string. This is the cited Koenig--Renner result in the convention printed by this paper.
-- source:
--   Unconditional privacy over channels which cannot convey quantum information, arXiv:quant-ph/0702077v1, PDF p. 16, Appendix Proposition 1: cited classical random-sampling bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P30

open QAlgorithms MeasureTheory

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise

attribute [local instance] Classical.decEq Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixContinuousENorm

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.matrixBorel

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P30.vectorBorel

/-- PDF p.16, Proposition 1, cited Lemma A.4 of Koenig--Renner (19).
The complete joint law is symmetric; the sample is the last k coordinates
of the SAME outcome, not an independent draw. The event uses full L1 and
>= epsilon. A positive sample size guards normalized empirical frequencies. -/
theorem symmetric_classical_sampling (n k w : ℕ) (hk : 0 < k) (hw : 0 < w)
    (p : (Fin (n + k) → Fin w) → ℝ)
    (hpos : ∀ out, 0 ≤ p out) (hsum : ∑ out, p out = 1)
    (hsym : ∀ (pi : Equiv.Perm (Fin (n + k))) out, p (out ∘ pi) = p out)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    (∑ out, if l1 (empiricalFrequency out)
        (empiricalFrequency (fun j : Fin k => out (Fin.natAdd n j))) ≥ epsilon
      then p out else 0) ≤
      (w : ℝ) * Real.exp (-((k : ℝ) * epsilon ^ 2) / (8 * (w : ℝ))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P30

end
