-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_Supplement_theorem_2
-- name    : RobustPrefLearn.MTP.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:13:26.853621+00:00
-- url     : https://prove2.me/theorems/cf7fdeb4-f2b0-4353-b1f5-92cf60270934
-- title:
--   Theorem 2 — finite-class accuracy and sample complexity (corrected: positive p)
-- statement:
--   Let $K\ge2$, $0<p<1$, and let $M_p^F$ be any finite subset of the published $p$-separable class $\mathcal M_p$. There is one family $\widehat\Pi=(\widehat\pi_\delta)_{\delta\in(0,1)}$ such that each $\widehat\pi_\delta$ is $\delta(M_p^F)$-accurate and, for every $f\in M_p^F$,
--   $$\mathbb E_f^{\widehat\pi_\delta}[\tau]<\infty\quad(0<\delta<1),\qquad \limsup_{\delta\downarrow0}\frac{\mathbb E_f^{\widehat\pi_\delta}[\tau]}{\log(1/\delta)}\le\frac1{I_*(f)}.$$
--   The information $I_*(f)$ uses alternatives in the full $\mathcal M_p$, not just the specified finite class. The family is selected after $M_p^F$ and before $\delta$ and $f$. This is an existence result; no particular implementation of Algorithm 2 is included in the statement. Empty finite classes and classes sharing one top item are allowed.
--
--   This theorem gives the pointwise asymptotic upper bound when the feasible preference class is finite, alongside finite expected stopping at every confidence level.
--
--   **Formalization Note** The published model and policies are reused unchanged. Their conventions use zero-based versions and ranks, distinct items in (A-3), newest-first histories, extended expectations and right-neighborhood limits. Accuracy is imposed only on $M_p^F$.
--
--   Differences from the source:
--   - correction: Definition 1 allows p=0 and prints (A-3) even for equal items → the published model with distinct-item (A-3), and 0<p<1; reason: equal-item (A-3) is inconsistent; at p=0 the published class is empty, so only the vacuous finite-class case is excluded; this is the planned base-mission convention
--   - encoding: a policy hat-pi indexed implicitly by delta, with f implicit in the theorem → one family chosen before delta and f, with all three conclusions on MF; reason: the proof on pp.51–52 explicitly quantifies f in MF and chooses a confidence-dependent threshold
--   - encoding: expectations and asymptotic rates → published ENNReal expectations and rate along delta down to zero; reason: infinite stopping expectations retain infinity, and log is evaluated eventually on 0<delta<1
-- source:
--   Feng, Caldentey & Ryan, SSRN 3215614, Theorem 2, p. 14; source.pdf sha256 5c09534e5696bccabf34ab8a3582c3ade8e448db308c84ee4895a5961f8629f1

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_Supplement_SubsetAccuracy

open scoped ENNReal

namespace RobustPrefLearn.MTP.Supplement

/-- Theorem 2, p.14. One δ-indexed family, accurate on every finite specified
subset, with finite expectations and the full-model information upper bound.
The family is selected before δ and f. Empty and single-top subsets are allowed. -/
theorem theorem_2 (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (MF : Set (Pref K)) (hfinite : MF.Finite) (hsub : MF ⊆ Mp p) :
    ∃ fam : ℝ → Policy K, AccurateOn MF fam ∧
      (∀ δ ∈ Set.Ioo (0 : ℝ) 1, ∀ f ∈ MF, expTau (fam δ) f < ⊤) ∧
      (∀ f ∈ MF, rate fam f ≤ (Istar p f)⁻¹) := by sorry

end RobustPrefLearn.MTP.Supplement
