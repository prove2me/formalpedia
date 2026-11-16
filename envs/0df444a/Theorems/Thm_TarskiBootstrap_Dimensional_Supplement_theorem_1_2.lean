-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_Supplement_theorem_1_2
-- name    : TarskiBootstrap.Dimensional.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:09:01.418677+00:00
-- url     : https://prove2.me/theorems/9b0b8e86-716d-4070-9683-fafe10112654
-- title:
--   Theorem 1.2 — Logarithmic hardness bootstrapping
-- statement:
--   Let $\mathcal F$ be a family of monotone self-maps of $[n]^k$, each with a unique fixed point, whose possible fixed points lie on an antichain $A$. Suppose $\Gamma_0$ is a nonnegative adversary matrix for $\mathrm{Tarski}(n,k)|_{\mathcal F}$ yielding a spectral lower bound of $\lambda/\delta$, $\delta>0$: $\|\Gamma_0\|\ge\lambda$ and $\|\Gamma_0\circ\Delta_x\|\le\delta$ for every query $x$. Then for every integer $m\ge2$ there are a family $\mathcal F'$ of monotone self-maps of $[nm]^{2k}$, each with a unique fixed point, and a nonnegative adversary matrix $\Gamma$ for $\mathrm{Tarski}(nm,2k)|_{\mathcal F'}$ with
--
--   $$
--   \|\Gamma\|\ \ge\ \mathrm{SA}(\mathrm{OS}_m)\,\lambda\qquad\text{and}\qquad\max_{x\in[nm]^{2k}}\|\Gamma\circ\Delta_x\|\ \le\ 2\delta,
--   $$
--
--   i.e. a spectral lower bound of $\mathrm{SA}(\mathrm{OS}_m)\lambda/(2\delta)$. Norms are spectral norms, and $\mathrm{SA}(\mathrm{OS}_m)$ is the spectral adversary value (2.8) of ordered search on $m$ positions.
--
--   Increasing the width from $n$ to $nm$ and the dimension from $k$ to $2k$ thus multiplies the nonnegative adversary bound by $\mathrm{SA}(\mathrm{OS}_m)=\Omega(\log m)$; the theorem does not claim that the fixed points of $\mathcal F'$ lie on an antichain.
--
--   Differences from the source:
--   - encoding: a hard instance family for Tarski(n, k) in which every function has a unique fixed point → F : Set (Grid n k → Grid n k) with every member monotone and having a unique fixed point; reason: Definition 2.1: instances are monotone self-maps of [n]^k; "hard" adds no assumption beyond the stated witness
--   - encoding: all possible fixed points lie on an antichain A → A antichain with possibleAnswers F ⊆ A; reason: literal transcription; the set of possible fixed points is the published possibleAnswers F
--   - encoding: an integer m ≥ 2 → m : ℕ+ with 2 ≤ m; reason: same values
--   - encoding: SA(OS_m) → osSA m, the spectral adversary value of the m ordered search strings with positions in Fin m; reason: Definition 2.2 and (2.8) transcribed
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Theorem 1.2, PDF/printed pp. 4–5; restated p. 17; proof pp. 17–23, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_OrderedSearch
import Definitions.Def_TarskiBootstrap_Dimensional_FixedPoint
import Definitions.Def_TarskiBootstrap_Dimensional_Witness

open scoped Matrix

namespace TarskiBootstrap.Dimensional.Supplement

/-- Theorem 1.2 (Logarithmic Hardness Bootstrapping Theorem), PDF/printed pp. 4–5
(restated p. 17, proof pp. 17–23). From a unique-fixed-point family `F` whose possible
fixed points lie on an antichain `A`, with a nonnegative adversary witness `λ/δ`, for
every `m ≥ 2` there is a family `F′` of monotone self-maps of `[nm]^{2k}` with unique
fixed points and a nonnegative adversary matrix `Γ` for `Tarski(nm, 2k)|F′` with
`‖Γ‖ ≥ SA(OS_m) λ` and `max_x ‖Γ ∘ Δ_x‖ ≤ 2δ`. -/
theorem theorem_1_2 {n k : ℕ+} (F : Set (Grid n k → Grid n k)) (A : Set (Grid n k))
    (hF : ∀ f : F, Monotone f.val ∧ ∃! x, f.val x = x)
    (hA : IsAntichain (· ≤ ·) A) (hcontains : possibleAnswers F ⊆ A)
    (lam δ : ℝ) (hδ : 0 < δ)
    (hwitness : ∃ Γ₀ : Matrix F F ℝ,
      NonnegativeAdversary (fun f : F => fixedPoint f.val) Γ₀ ∧
      SpectralWitness (fun f : F => f.val) Γ₀ lam δ)
    (m : ℕ+) (hm : 2 ≤ (m : ℕ)) :
    ∃ F' : Set (Grid (n * m) (2 * k) → Grid (n * m) (2 * k)),
      (∀ g : F', Monotone g.val ∧ ∃! x, g.val x = x) ∧
      ∃ Γ : Matrix F' F' ℝ,
        NonnegativeAdversary (fun g : F' => fixedPoint g.val) Γ ∧
        SpectralWitness (fun g : F' => g.val) Γ (osSA m * lam) (2 * δ) := by sorry

end TarskiBootstrap.Dimensional.Supplement
