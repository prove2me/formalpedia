-- Prove2me | Theorems.Thm_SetOptLattice_Existence_Supplement_proposition_4_11
-- name    : SetOptLattice.Existence.Supplement.proposition_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:59:19.152425+00:00
-- url     : https://prove2.me/theorems/fdc43762-d8ba-4934-900d-3dcbd8af4030
-- title:
--   Proposition 4.11 — full exact solution and Hausdorff limits, with the Min-plus variant under both readings
-- statement:
--   Let $X$ be a separated topological linear space over $\mathbb R$, $(Z,\preceq)$ a preordered set, $\Psi$ a family of monotone maps $Z\to\overline{\mathbb R}$, and $f:X\to\mathcal P(Z,\Psi)$. Suppose $f$ is $(0,\Psi)$-well-posed in the sense of Definition 4.9. Then
--   $$\operatorname{Min}(f,0,\Psi)\ne\varnothing,\qquad \operatorname{Min}(f,0,\Psi)\in\operatorname{Sol}(f,0,\Psi),$$
--   and both
--   $$\operatorname{Min}(f,\varepsilon,\Psi)\xrightarrow[\varepsilon\downarrow0]{H}\operatorname{Min}(f,0,\Psi),\qquad \operatorname{Min}(f,\varepsilon+,\Psi)\xrightarrow[\varepsilon\downarrow0]{H}\operatorname{Min}(f,0,\Psi).$$
--   In addition, $\operatorname{Min}(f,0+,\Psi)$ is nonempty and a $(0+,\Psi)$-solution, and $\operatorname{Min}(f,\varepsilon+,\Psi)\xrightarrow[\varepsilon\downarrow0]{H}\operatorname{Min}(f,0+,\Psi)$; this covers the reading of the paper's Min-plus sentence in which the $\varepsilon=0$ instance is replaced as well.
--   Here $H$ denotes two-sided neighborhood Hausdorff convergence: for every neighborhood $U$ of zero, both inclusions in the respective Minkowski enlargements hold eventually. Both limits are the ordinary exact minimizer set.
--
--   This proposition supplies condition (1) in the forward implication of Theorem 4.12 and records stability of the full minimizer sets. No extra assumption that $\Psi$ is nonempty is needed: it follows from well-posedness and the nonempty exact solution it requires.
--
--   Differences from the source:
--   - encoding: arbitrary directed nets and genuine cofinal subnets → nontrivial image-tail filters and nontrivial finer filters on the set-valued carrier; reason: every such filter has a directed-net realization, and refinements lift to cofinal subnets of any original representing net; this avoids a bound on index universes
--   - reading: Hausdorff convergence without a standalone definition → both eventual neighborhood inclusions, with positive tolerances tending to zero; reason: the proof on p. 24 fixes this meaning; no metric or closed/bounded set restriction is introduced
--   - reading: Definition 4.8: "for all i > i_ε" (strict) the set M_i is an (ε,Ψ)-solution → eventually along the tail filter (all i ≥ i_ε); reason: the usual net tail; under the strict reading every net with a largest index would be Ψ-minimizing vacuously, so arbitrary constant nets would have to converge to solutions, which the paper (Example 4.10, proofs on pp. 27–28) does not intend
--   - generalization: "The above result remains true if Min (f, ε, Ψ) is replaced by Min (f, ε+, Ψ)" (p. 27), which may or may not replace the ε = 0 instance Min (f, 0, Ψ) → both readings are stated: Min (f, ε+, Ψ) → Min (f, 0, Ψ), and also Min (f, 0+, Ψ) nonempty, a (0+, Ψ)-solution, with Min (f, ε+, Ψ) → Min (f, 0+, Ψ); reason: the sentence is ambiguous; the conjunction specializes to the source claim under either reading
-- source:
--   Crespi, Hamel, Rocca, Schrage, arXiv:1812.03300v1, p. 27, Proposition 4.11 and its following Min-plus variant

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Supplement_WellPosedness

namespace SetOptLattice.Existence.Supplement

/-- Proposition 4.11, p. 27, together with its immediately following Min-plus variant.
The variant is stated under both readings of "Min (f, ε, Ψ) is replaced by Min (f, ε+, Ψ)":
only the positive-tolerance family replaced (fourth conjunct), and also the ε = 0 instance
replaced, i.e. Min (f, 0+, Ψ) nonempty, a (0+, Ψ)-solution, and the Min-plus limit (last conjunct). -/
theorem proposition_4_11 {X Z : Type*} [Preorder Z]
    [AddCommGroup X] [Module ℝ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℝ X] [T2Space X]
    (Ψ : Set (Z → EReal)) (hΨ : ∀ ψ ∈ Ψ, Monotone ψ)
    (f : X → Set Z) (hf : ∀ x, IsPsiClosed Ψ (f x))
    (hwp : IsWellPosed Ψ f) :
    (MinSet Ψ f 0).Nonempty ∧ IsSolution Ψ f 0 (MinSet Ψ f 0) ∧
      HausdorffConverges (MinSet Ψ f) (MinSet Ψ f 0) ∧
      HausdorffConverges (MinPlusSet Ψ f) (MinSet Ψ f 0) ∧
      ((MinPlusSet Ψ f 0).Nonempty ∧ IsPlusSolution Ψ f 0 (MinPlusSet Ψ f 0) ∧
        HausdorffConverges (MinPlusSet Ψ f) (MinPlusSet Ψ f 0)) := by sorry

end SetOptLattice.Existence.Supplement
