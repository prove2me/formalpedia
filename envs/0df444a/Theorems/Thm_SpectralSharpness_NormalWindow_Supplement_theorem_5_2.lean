-- Prove2me | Theorems.Thm_SpectralSharpness_NormalWindow_Supplement_theorem_5_2
-- name    : SpectralSharpness.NormalWindow.Supplement.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:18:00.794192+00:00
-- url     : https://prove2.me/theorems/2c6bfff3-5649-43af-bbfc-fffe7885e7b1
-- title:
--   Theorem 5.2 — the halting problem sits on the boundary
-- statement:
--   Let M range over Mathlib’s standard acceptable codes for partial recursive machines, at fixed input zero. Use bounded evaluation to define α_t and the infinite sum α. The label at x is +1 if x<α and −1 otherwise, including at a tie. The construction is uniform in the machine code.
--
--   Theorem 5.2 (the halting problem sits on the boundary). For a Turing machine M define
--   the rational numbers
--   α_t = ∑_{n=1}^t 2^(−n) · [[ M halts within n steps ]], α = lim_{t→∞} α_t.
--   Then |α − α_t| ≤ 2^(−t), so α is a computable real; and for the ideal classifier with boundary α,
--   H_α(0) = +1 ⇐⇒ 0 < α ⇐⇒ M halts.
--   Hence the classification map M ↦ H_α(0) is many-one equivalent to the halting problem. Even though
--   the boundary is a computable real given with a computable modulus of convergence, no Turing
--   machine determines the label of the single point x = 0.
--
--   $$
--   \alpha_t=\sum_{n=1}^t2^{-n}\mathbf1_{\{M\text{ halts within }n\}},\quad |\alpha-\alpha_t|\le2^{-t},\quad H_\alpha(0)=+1\iff0<\alpha\iff M\text{ halts}.
--   $$
--
--   This statement supplies the source’s independent companion result alongside the published normal-window goal.
--
--   Differences from the source:
--   - encoding: a standard Turing machine, finite step simulation and many-one equivalence → Mathlib acceptable partial-recursive machine codes, bounded evaluation and total computable reductions; reason: this changes the acceptable encoding, not the halting set or real Cauchy representation
--   - reading: H_α(0)=+1 iff 0<α → H_α(x)=+1 for x<α and −1 otherwise; reason: the theorem fixes the orientation and tie only at zero; this extension preserves every evaluated instance
-- source:
--   Wenwei Li, The Spectral Cost of Sharpness: Fourier Truncation, the Gibbs Bend, and the Computability of Classification, 2026 manuscript, STOC 2027 submission #122, SHA-256 0c0e3d52a54d9fbebc999feaa9b26703db76a5586d3c43db2ed20b17c15a9100, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/122.pdf, Theorem 5.2, p. 12

import Mathlib
import Definitions.Def_SpectralSharpness_NormalWindow_Supplement_Computability

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SpectralSharpness.NormalWindow.Supplement

theorem theorem_5_2 :
    (∀ M : Machine, ∀ t, |haltingBoundary M-(boundaryApprox M t:ℝ)| ≤ (2:ℝ)^(-(t:ℤ))) ∧
    (Computable (fun p : Machine × ℕ => boundaryApprox p.1 p.2)) ∧
    (∀ M : Machine, DetParamSVP.IsComputableReal (haltingBoundary M)) ∧
    (∀ M : Machine, (boundaryLabel M 0=1 ↔ 0 < haltingBoundary M) ∧
      (0 < haltingBoundary M ↔ halts M)) ∧
    manyOneEquivalent (fun M : Machine => boundaryLabel M 0=1) halts ∧
    ¬ ∃ c : Machine → Bool, Computable c ∧ ∀ M, (c M=true ↔ boundaryLabel M 0=1) := by sorry

end SpectralSharpness.NormalWindow.Supplement
