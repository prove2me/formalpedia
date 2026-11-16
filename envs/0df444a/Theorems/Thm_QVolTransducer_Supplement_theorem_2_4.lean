-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_2_4
-- name    : QVolTransducer.Supplement.theorem_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:34:23.015517+00:00
-- url     : https://prove2.me/theorems/6adfbf91-e324-4694-bb95-be78f1b1c561
-- title:
--   Theorem 2.4 — reflection problems: one vector per input gives a bidirectional adversary solution
-- statement:
--   Let $P=\{(|\psi_x\rangle,|\psi_x\rangle,O_x)\}_{x\in\mathcal D_+}\cup\{(|\psi_x\rangle,-|\psi_x\rangle,O_x)\}_{x\in\mathcal D_-}$ be a state-conversion problem (a **reflection problem**), and suppose $\{|w_x^+\rangle\}_{x\in\mathcal D_+}\cup\{|w_x^-\rangle\}_{x\in\mathcal D_-}\subseteq\mathcal H\otimes\mathcal W$ satisfy
--
--   $$\langle w_x^+|(I-O_x^\dagger O_y)|w_y^-\rangle=2\langle\psi_x|\psi_y\rangle\qquad\text{for all }(x,y)\in\mathcal D_+\times\mathcal D_-.$$
--
--   Then $P$ has a feasible solution to the bidirectional adversary bound, with workspace $\mathcal W\otimes\mathbb C^2$, whose cost $c$ satisfies
--
--   $$c^2\le\sup_{x\in\mathcal D_+}\||w_x^+\rangle\|^2\cdot\sup_{x\in\mathcal D_-}\||w_x^-\rangle\|^2,\qquad\text{so}\qquad \overleftrightarrow{\mathrm{ADV}}(P)\le\sqrt{\max_{x\in\mathcal D_+}\||w_x^+\rangle\|^2\cdot\max_{x\in\mathcal D_-}\||w_x^-\rangle\|^2}.$$
--
--   For reflection problems only one vector per input is needed, and the costs of the two classes can be rebalanced; this simplifies every adversary-bound construction of Section 3.
--
--   **Formalization Note** The index set $\mathcal D_+\cup\mathcal D_-$ is the disjoint union, with states, oracles and vectors given on each part. Suprema and the cost are taken in $[0,\infty]$ (with $0\cdot\infty=0$), which covers empty $\mathcal D_\pm$ and zero vectors.
--
--   Differences from the source:
--   - encoding: index set D₊ ∪ D₋ → the disjoint union Dp ⊕ Dm, with ψ, O and w given on each part; reason: each input lies in exactly one class of a reflection problem; same instances
--   - encoding: Hilbert spaces H (oracle) and the state space → ℂ^H and ℂ^V for finite types; the workspace W is any complex Hilbert space; reason: Part I's oracle and state spaces are finite-dimensional (pp.4, 36); W is kept general as in Definition 2.2
--   - generalization: ADV↔(P) ≤ √(max_{D₊}‖w⁺‖² · max_{D₋}‖w⁻‖²) → a feasible solution in H ⊗ (W ⊗ ℂ²) exists whose cost c (a sup in [0,∞]) satisfies c² ≤ sup_{D₊}‖w⁺‖² · sup_{D₋}‖w⁻‖²; reason: ADV↔ is the least cost of a feasible solution (Definition 2.2), so an explicit solution of that cost implies the printed bound; max is read as sup since the maxima need not be attained for infinite D±
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 2.4, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_QVolTransducer_Supplement_IsBiAdvSolution

namespace QVolTransducer.Supplement

open scoped ENNReal

/-- **Reflection problems: one vector per input suffices** (Cornelissen, Apers, Gribling,
*Improved quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217
(version of November 3, 2026, sha256 40d7b52d…), Theorem 2.4, p.12 (PDF p.14)).

Let `P = {(|ψ_x⟩, |ψ_x⟩, O_x)}_{x∈D₊} ∪ {(|ψ_x⟩, −|ψ_x⟩, O_x)}_{x∈D₋}` be a state-conversion
problem, and suppose `{|w_x^+⟩}_{x∈D₊} ∪ {|w_x^−⟩}_{x∈D₋} ⊆ ℋ ⊗ 𝒲` satisfy
`⟨w_x^+| (I − O_x†O_y) |w_y^−⟩ = 2⟨ψ_x|ψ_y⟩` for all `(x, y) ∈ D₊ × D₋`. Then `P` has a feasible
solution to the bidirectional adversary bound, in `ℋ ⊗ (𝒲 ⊗ ℂ²)`, whose cost `c` satisfies
`c² ≤ sup_{x∈D₊} ‖|w_x^+⟩‖² · sup_{x∈D₋} ‖|w_x^−⟩‖²`; in particular
`ADV↔(P) ≤ √(max_{x∈D₊} ‖|w_x^+⟩‖² · max_{x∈D₋} ‖|w_x^−⟩‖²)`.

**Formalization Note** The index set `D₊ ∪ D₋` is the disjoint union `D₊ ⊕ D₋`, with states,
oracles and vectors given separately on both parts. The oracle space is `ℂ^H` (finite `H`), the
states lie in `ℂ^V`, and the workspace `𝒲` is an arbitrary complex Hilbert space; `D₊, D₋` are
arbitrary. Suprema and the cost are in `ℝ≥0∞` (`0 · ∞ = 0`), which covers empty `D_±` and zero
vectors. The conclusion exhibits the feasible solution that bounds `ADV↔(P)` (Definition 2.2). -/
theorem theorem_2_4 {H V W Dp Dm : Type} [Fintype H] [DecidableEq H] [Fintype V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (ψp : Dp → EuclideanSpace ℂ V) (ψm : Dm → EuclideanSpace ℂ V)
    (Op : Dp → Matrix.unitaryGroup H ℂ) (Om : Dm → Matrix.unitaryGroup H ℂ)
    (wp : Dp → TensorW H W) (wm : Dm → TensorW H W)
    (hw : ∀ x y, advForm (Op x : Matrix H H ℂ) (Om y) (wp x) (wm y) =
      2 * inner ℂ (ψp x) (ψm y)) :
    ∃ vp vm : Dp ⊕ Dm → TensorW H (TensorW (Fin 2) W),
      IsBiAdvSolution (Sum.elim ψp ψm) (Sum.elim ψp (fun y => -ψm y))
        (fun z => ((Sum.elim Op Om z : Matrix.unitaryGroup H ℂ) : Matrix H H ℂ)) vp vm ∧
      biAdvCost vp vm ^ 2 ≤
        (⨆ x, ENNReal.ofReal (‖wp x‖ ^ 2)) * (⨆ y, ENNReal.ofReal (‖wm y‖ ^ 2)) := by sorry

end QVolTransducer.Supplement
