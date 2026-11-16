-- Prove2me | Theorems.Thm_TarskiBootstrap_Dimensional_Supplement_theorem_1_3
-- name    : TarskiBootstrap.Dimensional.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:09:53.185712+00:00
-- url     : https://prove2.me/theorems/5fa4512d-dd4e-4eb9-b4e4-27dca35b8fc8
-- title:
--   Theorem 1.3 — Antichain lifting
-- statement:
--   Let $\mathcal F$ be a family of monotone self-maps of $[n]^k$, each with a unique fixed point, and let $\Gamma_0$ be a nonnegative adversary matrix for $\mathrm{Tarski}(n,k)|_{\mathcal F}$ yielding a spectral lower bound of $\lambda/\delta$, $\delta>0$. Then every function in $\mathcal B(\mathcal F)$ is a monotone self-map of $[n]^{2k}$ with a unique fixed point, all possible fixed points of $\mathcal B(\mathcal F)$ lie on an antichain, and there is a nonnegative adversary matrix $\Gamma$ for $\mathrm{Tarski}(n,2k)|_{\mathcal B(\mathcal F)}$ with
--
--   $$
--   \|\Gamma\|\ \ge\ \lambda\qquad\text{and}\qquad\max_{z\in[n]^{2k}}\|\Gamma\circ\Delta_z\|\ \le\ 2\delta,
--   $$
--
--   i.e. a spectral lower bound of $\lambda/(2\delta)$. Here $\mathcal B(f)(x,y)=(f(x),\overline{f(\bar y)})$ and norms are spectral norms.
--
--   The transformation makes any unique-fixed-point hard family satisfy the antichain hypothesis of the two bootstrapping theorems at the cost of doubling the dimension and a factor $2$.
--
--   Differences from the source:
--   - encoding: a hard instance family for Tarski(n, k) in which every function has a unique fixed point → F : Set (Grid n k → Grid n k) with every member monotone and having a unique fixed point; reason: Definition 2.1: instances are monotone self-maps of [n]^k; "hard" adds no assumption beyond the stated witness
--   - encoding: [n]^{2k} → Grid n k × Grid n k with the product order; reason: order-isomorphic to the coordinatewise order on 2k coordinates (flattenBlocks n k 2)
--   - encoding: "all possible fixed points lie on an antichain" → IsAntichain of possibleAnswers (B(F)); reason: a set lies on an antichain iff it is an antichain
-- source:
--   Li, Ma, Yang and Zhao, Bootstrapping Classical and Quantum Query Lower Bounds for Finding Tarski Fixed Points, STOC 2027 submission #6 (2026), frozen preprint, Theorem 1.3, PDF/printed p. 5; restated and proved p. 16, SHA-256 320afa8333f95589a388b30ffbfd6d7b7e5d93cdf07fa8630825fbf7d0107d59; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/6.pdf. Printed page = PDF page. No arXiv identifier/version supplied.

import Definitions.Def_TarskiBootstrap_Dimensional_Supplement_AntichainConstructor
import Definitions.Def_TarskiBootstrap_Dimensional_Witness

open scoped Matrix

namespace TarskiBootstrap.Dimensional.Supplement

/-- Theorem 1.3, PDF/printed p. 5 (restated and proved p. 16). For a unique-fixed-point
family `F` with a nonnegative adversary witness `λ/δ`, the image family `B(F)` consists of
monotone self-maps of `[n]^{2k}` with unique fixed points, its possible fixed points form
an antichain, and some nonnegative adversary matrix `Γ` for `Tarski(n, 2k)|B(F)` has
`‖Γ‖ ≥ λ` and `max_z ‖Γ ∘ Δ_z‖ ≤ 2δ`. -/
theorem theorem_1_3 {n k : ℕ+} (F : Set (Grid n k → Grid n k))
    (hF : ∀ f : F, Monotone f.val ∧ ∃! x, f.val x = x)
    (lam δ : ℝ) (hδ : 0 < δ)
    (hwitness : ∃ Γ₀ : Matrix F F ℝ,
      NonnegativeAdversary (fun f : F => fixedPoint f.val) Γ₀ ∧
      SpectralWitness (fun f : F => f.val) Γ₀ lam δ) :
    (∀ g : antichainFamily F, Monotone g.val ∧ ∃! p, g.val p = p) ∧
    IsAntichain (· ≤ ·) (possibleAnswers (antichainFamily F)) ∧
    ∃ Γ : Matrix (antichainFamily F) (antichainFamily F) ℝ,
      NonnegativeAdversary (fun g : antichainFamily F => fixedPoint g.val) Γ ∧
      SpectralWitness (fun g : antichainFamily F => g.val) Γ lam (2 * δ) := by sorry

end TarskiBootstrap.Dimensional.Supplement
