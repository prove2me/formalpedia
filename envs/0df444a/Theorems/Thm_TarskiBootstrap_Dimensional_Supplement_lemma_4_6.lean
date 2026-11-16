-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_Supplement_lemma_4_6
-- name    : TarskiBootstrap.Dimensional.Supplement.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:07:44.559928+00:00
-- url     : https://prove2.me/theorems/ced5a19b-fd78-4c36-8df0-e13c6bdfc5f6
-- title:
--   Lemma 4.6 — Composition with ordered search
-- statement:
--   Let $\mathcal F$, $A$ be as in Lemma 4.3 and $\mathcal F'$ the hidden-sign family. For every integer $m\ge2$, the composite problem $\mathrm{OS}_m\circ(\mathrm{Tarski}^H(n,k)|_{\mathcal F'},\dots,\mathrm{Tarski}^H(n,k)|_{\mathcal F'})$ with $m$ copies, on its domain (2.13), admits a nonnegative adversary matrix $\Gamma$ whose adversary ratio $\|\Gamma\|/\max_i\|\Gamma\circ\Delta_i\|$ is at least $\mathrm{SA}(\mathrm{OS}_m)\cdot\mathrm{SA}(\mathrm{Tarski}^H(n,k)|_{\mathcal F'})$; consequently
--
--   $$
--   \mathrm{SA}\bigl(\mathrm{OS}_m\circ(\mathrm{Tarski}^H(n,k)|_{\mathcal F'},\dots,\mathrm{Tarski}^H(n,k)|_{\mathcal F'})\bigr)\ \ge\ \mathrm{SA}(\mathrm{OS}_m)\cdot\mathrm{SA}\bigl(\mathrm{Tarski}^H(n,k)|_{\mathcal F'}\bigr).
--   $$
--
--   This is the step at which ordered search multiplies the adversary bound; it is an application of the composition theorem of Phillips (Theorem 2.10, cited from [Phi26]).
--
--   Differences from the source:
--   - encoding: a hard instance family for Tarski(n, k) in which every function has a unique fixed point → F : Set (Grid n k → Grid n k) with every member monotone and having a unique fixed point; reason: Definition 2.1: instances are monotone self-maps of [n]^k; "hard" adds no assumption beyond the stated witness
--   - encoding: all possible fixed points lie on an antichain A → A antichain with possibleAnswers F ⊆ A; reason: literal transcription; the set of possible fixed points is the published possibleAnswers F
--   - encoding: an integer m ≥ 2 → m : ℕ+ with 2 ≤ m; reason: same values
--   - encoding: positions and block indices 1, …, m → Fin m = {0, …, m-1}; reason: order-preserving reindexing
--   - encoding: SA as the maximum (2.8) over nonzero nonnegative adversary matrices, 0 for a constant function → real sSup of the ratio set (sSup ∅ = 0); reason: the ratio set is bounded by |I| and the maximum is attained, so the supremum equals the maximum; empty set ↔ constant function
--   - encoding: "admits a nonnegative adversary matrix Γ witnessing the lower bound (4.7)" → a conjunction: ∃ Γ nonnegative adversary with ratio ≥ SA(OS_m) · SA(Tarski^H|F′), and (4.7); reason: both readings of the sentence are stated
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Lemma 4.6 and equation (4.7), PDF/printed p. 19, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_Composite

open scoped Matrix

namespace TarskiBootstrap.Dimensional.Supplement

open scoped Classical

/-- Lemma 4.6, PDF/printed p. 19: for every integer `m ≥ 2`, the composition
`OS_m ∘ (Tarski^H(n,k)|F′, …, Tarski^H(n,k)|F′)` (domain (2.13)) admits a nonnegative
adversary matrix whose ratio (2.8) is at least `SA(OS_m) · SA(Tarski^H(n,k)|F′)`, and
hence (4.7) holds. -/
theorem lemma_4_6 {n k : ℕ+} (F : Set (Grid n k → Grid n k)) (A : Set (Grid n k))
    (hF : ∀ f : F, Monotone f.val ∧ ∃! x, f.val x = x)
    (hA : IsAntichain (· ≤ ·) A) (hcontains : possibleAnswers F ⊆ A)
    (m : ℕ+) (hm : 2 ≤ (m : ℕ)) :
    (∃ Γ : Matrix (compositeDomain A F m) (compositeDomain A F m) ℝ,
      NonnegativeAdversary
        (fun x : compositeDomain A F m => compositeAnswer m x.val) Γ ∧
      osSA m * spectralAdversary (hiddenSignFamily A F) tarskiHAnswer ≤
        adversaryRatio (fun x : compositeDomain A F m => x.val) Γ) ∧
    osSA m * spectralAdversary (hiddenSignFamily A F) tarskiHAnswer ≤
      spectralAdversary (compositeDomain A F m) (compositeAnswer m) := by sorry

end TarskiBootstrap.Dimensional.Supplement
