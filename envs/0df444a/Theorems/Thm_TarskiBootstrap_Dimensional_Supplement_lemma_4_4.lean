-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_Supplement_lemma_4_4
-- name    : TarskiBootstrap.Dimensional.Supplement.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:06:50.228209+00:00
-- url     : https://prove2.me/theorems/2a4e290d-245b-4479-b061-ab4b8bdc68b7
-- title:
--   Lemma 4.4 — Triangle-tensor adversary for the hidden sign
-- statement:
--   Let $\mathcal F$, $A$ be as in Lemma 4.3, and let $\Gamma_0$ be a nonnegative adversary matrix for $\mathrm{Tarski}(n,k)|_{\mathcal F}$ yielding a spectral lower bound of $\lambda/\delta$, $\delta>0$. Label $\mathcal F'=H_{-1}(\mathcal F)\sqcup H_0(\mathcal F)\sqcup H_1(\mathcal F)$ by $(s,f)$, with oracle $(s,f)\mapsto\bigl(x\mapsto(f(x),\sigma^f_s(x))\bigr)$ and answer $\mathrm{Tarski}^H(s,f)=\sigma^f_s(f^*)$. Then $\Gamma=K_3\otimes\Gamma_0$ is a nonnegative adversary matrix for $\mathrm{Tarski}^H(n,k)|_{\mathcal F'}$ and
--
--   $$
--   \|\Gamma\|\ge2\lambda\qquad\text{and}\qquad\|\Gamma\circ\Delta'_x\|\le2\delta\quad\text{for every }x\in[n]^k,
--   $$
--
--   so $\Gamma$ yields the spectral lower bound $(2\lambda)/(2\delta)=\lambda/\delta$.
--
--   The hidden-sign problem therefore keeps the adversary ratio of the original family; it is the inner problem composed with ordered search.
--
--   Differences from the source:
--   - encoding: a hard instance family for Tarski(n, k) in which every function has a unique fixed point → F : Set (Grid n k → Grid n k) with every member monotone and having a unique fixed point; reason: Definition 2.1: instances are monotone self-maps of [n]^k; "hard" adds no assumption beyond the stated witness
--   - encoding: all possible fixed points lie on an antichain A → A antichain with possibleAnswers F ⊆ A; reason: literal transcription; the set of possible fixed points is the published possibleAnswers F
--   - reading: Γ "yields a spectral lower bound of λ/δ" → SpectralWitness for Γ with the pair (2λ, 2δ); reason: the proof (4.5)–(4.6) establishes ‖Γ‖ ≥ 2λ and ‖Γ ∘ Δ′_x‖ ≤ 2δ and concludes "(2λ)/(2δ) = λ/δ"; the literal pair (λ, δ) fails for the unscaled Γ (F = {f1, f2} with distinct fixed points, Γ0 = [[0,1],[1,0]], λ = δ = 1 and f1(x) ≠ f2(x) give ‖Γ ∘ Δ′_x‖ = 2 > δ), so the ratio reading is the one the page proves
--   - encoding: F′ = H_{−1}(F) ⊔ H_0(F) ⊔ H_1(F) as a set of Tarski* instances → inputs indexed by labels (s, f) ∈ SignType × F; reason: the source labels F′ uniquely by (s, f) and indexes Γ by the labels (p. 18)
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Lemma 4.4, PDF/printed p. 18; proof (4.5)–(4.6), p. 18, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_HiddenSign
import Definitions.Def_TarskiBootstrap_Dimensional_Witness

open scoped Matrix

namespace TarskiBootstrap.Dimensional.Supplement

/-- Lemma 4.4, PDF/printed p. 18, in the reading its proof establishes ((4.5), (4.6)):
`Γ = K_3 ⊗ Γ_0`, indexed by the labels `(s, f)` of `F′`, is a nonnegative adversary
matrix for `Tarski^H(n, k)|F′` with `‖Γ‖ ≥ 2λ` and `‖Γ ∘ Δ′_x‖ ≤ 2δ` for every `x`,
i.e. a spectral lower bound of `(2λ)/(2δ) = λ/δ`. -/
theorem lemma_4_4 {n k : ℕ+} (F : Set (Grid n k → Grid n k)) (A : Set (Grid n k))
    (hF : ∀ f : F, Monotone f.val ∧ ∃! x, f.val x = x)
    (hA : IsAntichain (· ≤ ·) A) (hcontains : possibleAnswers F ⊆ A)
    (Γ₀ : Matrix F F ℝ) (lam δ : ℝ) (hδ : 0 < δ)
    (hΓ₀ : NonnegativeAdversary (fun f : F => fixedPoint f.val) Γ₀)
    (hw : SpectralWitness (fun f : F => f.val) Γ₀ lam δ) :
    NonnegativeAdversary
        (fun p : SignType × F => tarskiHAnswer (hiddenSignOracle A p.1 p.2.val))
        (hiddenSignAdversary Γ₀) ∧
      SpectralWitness (fun p : SignType × F => hiddenSignOracle A p.1 p.2.val)
        (hiddenSignAdversary Γ₀) (2 * lam) (2 * δ) := by sorry

end TarskiBootstrap.Dimensional.Supplement
