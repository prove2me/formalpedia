-- Prove2me | Theorems.Thm_SpectralFeedback_lemma_H_1_active_reduction
-- name    : SpectralFeedback.lemma_H_1_active_reduction
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:28:56.229307+00:00
-- url     : https://prove2.me/theorems/a9b09343-ee60-4484-be03-3f8a888c3108
-- title:
--   Lemma H.1 — active reduction: $\mathcal G^F_{m,s}(R)=\mathcal G^F_{m,s}(R_{[q]})$, $q=\min(d,ms)$
-- statement:
--   Let $m,s\ge1$, let $R\succeq0$ act on $\mathbb C^d$, and let $F:\mathbb R^s_+\to\mathbb R$ be continuous and coordinatewise nondecreasing. Put $q=\min(d,ms)$ and let $R_{[q]}$ retain the first $q$ eigenvalues of $R$ with their original mass (in a decreasing spectral basis). Then both maxima exist and
--
--   $$
--   \mathcal G^F_{m,s}(R)=\mathcal G^F_{m,s}(R_{[q]}).
--   $$
--
--   Moreover:
--
--   1. the active problem (for $R_{[q]}$) has an optimizer whose $m$ atoms all have rank at most $s$;
--   2. if $(A_1,\dots,A_m)$ is any optimizer of the active problem and $h_0$ is any index, then replacing $A_{h_0}$ by $A_{h_0}+(R-R_{[q]})$ gives a decomposition of $R$ into positive semidefinite atoms that attains $\mathcal G^F_{m,s}(R)$.
--
--   The lemma reduces any $m$-atom spectral program to the leading $\min(d,ms)$ eigenvalues and to atoms of rank at most $s$; Theorem H.2 applies it with $m=2$.
--
--   **Formalization Note** "$\mathcal G=v$" is `IsGreatest (rewardSet s F m ·) v`. $R_{[q]}$ is `activePart R U q` for an arbitrary decreasing spectral basis $U$; the statement holds for every such $U$.
--
--   Differences from the source:
--   - encoding: matrices on $\mathbb C^d$, eigenvalues $\lambda_i$ ($1$-based, padded by zeros) → `Matrix (Fin d) (Fin d) ℂ` for every `d : ℕ`; `eigDesc A (i-1)` (0-based, padded by zeros); reason: Lean indexing convention; same instances
--   - encoding: $\mathcal G^F_{m,s}(R)=\mathcal G^F_{m,s}(R_{[q]})$ (maxima of the reward sets) → ∃ v, `IsGreatest (rewardSet s F m R) v ∧ IsGreatest (rewardSet s F m (activePart R U (min d (m*s)))) v`; reason: the maximum exists (as §H.1.1 says) and the two maxima agree; same content
--   - encoding: $R_{[q]}$ retains the first $q$ eigenvalues with their original mass → `activePart R U q` for every unitary `U` with `R = U diag(λ) U*`; reason: under ties the truncation depends on the eigenbasis; the statement holds for each choice
--   - generalization: $F$ admissible (continuous, symmetric, concave, coordinatewise nondecreasing, $F(0)=0$, values in $\mathbb R_+$) → $F$ only `ContinuousOn` and `MonotoneOn` the orthant; reason: the lemma states that it uses only continuity and coordinate monotonicity, and its proof uses nothing else; every admissible $F$ satisfies the weaker hypotheses, so it specializes to the source
--   - reading: Adding $R-R_{[q]}$ to one active atom produces a full-input optimizer → for every optimizer of the active problem and every atom index $h_0$, the updated family is PSD, sums to $R$ and attains the value; reason: "one active atom" is read as any atom (the stronger reading); the proof's pooling step works for every atom
-- source:
--   Qi, Spectral Structure and Exact Arithmetic of Finite-Feedback Measurement Discrimination, manuscript (Nov. 2026; PDF sha256 a5b5cf40…eabde9cf), Lemma H.1, pp.108–109 (PDF pp.110–111); main-text Theorem 4.1, p.6 (PDF p.8)

import Mathlib
import Definitions.Def_SpectralFeedback_rewardSet
import Definitions.Def_SpectralFeedback_pairAtom

open scoped ComplexOrder

namespace SpectralFeedback

/-- **Lemma H.1** (Active reduction for monotone rewards; Qi, *Spectral Structure and Exact
Arithmetic of Finite-Feedback Measurement Discrimination*, manuscript (Nov. 2026), pp.108–109 (PDF
pp.110–111); main-text twin Theorem 4.1, p.6). Let `q = min(d, ms)` and let `R_{[q]}` retain the
first `q` eigenvalues of `R ⪰ 0` with their original mass. Then `G^F_{m,s}(R) = G^F_{m,s}(R_{[q]})`.
The active problem has an optimizer whose `m` atoms have rank at most `s`. Adding `R − R_{[q]}` to
one active atom produces a full-input optimizer.

**Formalization Note** `G^F_{m,s}(·) = v` is `IsGreatest (rewardSet s F m ·) v`; `R_{[q]}` is
`activePart R U q` for an arbitrary decreasing spectral basis `U` of `R` (the statement holds for
every such `U`). The hypotheses on `F` are only continuity and coordinatewise monotonicity on
`ℝ^s_+`, as the lemma's last sentence says it uses; concavity, symmetry, `F(0) = 0` and `F ≥ 0` are
not assumed. "One active atom" is read as any atom `h₀` of any active optimizer. -/
theorem lemma_H_1_active_reduction (m s : ℕ) (hm : 1 ≤ m) (hs : 1 ≤ s) {d : ℕ}
    (R : Matrix (Fin d) (Fin d) ℂ) (hR : R.PosSemidef)
    (U : Matrix (Fin d) (Fin d) ℂ) (hU : IsSortedEigenbasis R U)
    (F : (Fin s → ℝ) → ℝ) (hFc : ContinuousOn F (orthant s)) (hFm : MonotoneOn F (orthant s)) :
    ∃ v : ℝ,
      IsGreatest (rewardSet s F m R) v ∧
      IsGreatest (rewardSet s F m (activePart R U (min d (m * s)))) v ∧
      (∃ A : Fin m → Matrix (Fin d) (Fin d) ℂ, (∀ h, (A h).PosSemidef) ∧
        ∑ h, A h = activePart R U (min d (m * s)) ∧ ∑ h, reward s F (A h) = v ∧
        ∀ h, (A h).rank ≤ s) ∧
      (∀ A : Fin m → Matrix (Fin d) (Fin d) ℂ, (∀ h, (A h).PosSemidef) →
        ∑ h, A h = activePart R U (min d (m * s)) → ∑ h, reward s F (A h) = v →
        ∀ h₀ : Fin m,
          (∀ h, (Function.update A h₀ (A h₀ + (R - activePart R U (min d (m * s)))) h).PosSemidef) ∧
          ∑ h, Function.update A h₀ (A h₀ + (R - activePart R U (min d (m * s)))) h = R ∧
          ∑ h, reward s F (Function.update A h₀ (A h₀ + (R - activePart R U (min d (m * s)))) h)
            = v) := by sorry

end SpectralFeedback
