-- Prove2me | Theorems.Thm_QVolKLS_Supplement_theorem_3_1
-- name    : QVolKLS.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:34:31.340894+00:00
-- url     : https://prove2.me/theorems/f5efa23b-70ca-410c-9de9-f7fe35f5e505
-- title:
--   Theorem 3.1 — slow-spectrum bound from uniform warm-start mixing
-- statement:
--   There is an absolute constant $C>0$ with the following property. Let $P$ be a positive, ergodic, reversible Markov operator on an arbitrary measurable space with stationary probability law $\pi$. Suppose every two-warm start mixes to total-variation error at most $\eta\in(0,1/2)$ by time $t\ge1$. Let $\Pi_{\mathrm{slow}}$ be the nonstationary spectral projection at eigenvalues in $[1-1/(2t),1)$, and let $\Pi_{\mathrm{slow}}\otimes I_A$ act on vector fields with values in a finite-dimensional or separable auxiliary Hilbert space. Then
--   $$
--   \| (\Pi_{\mathrm{slow}}\otimes I_A)\Psi\|_{2,\pi}
--     \le C\eta^{1/4}\|\Psi\|_{4,\pi}.
--   $$
--
--   This turns uniform warm-start mixing into quantitative control of every nonstationary slow spectral component.
--
--   **Formalization Note** The vector field is represented after the unitary density identification $J_\pi$, so $J_\pi$ and $J_\pi^\dagger$ disappear from the displayed action. Both moment quantities use nonnegative integrals, hence a nonintegrable fourth moment is $+\infty$. The measurability inherent in a joint vector and its projected component is explicit.
--
--   Differences from the source:
--   - encoding: the source writes $J_\pi\Pi_{\mathrm{slow}}J_\pi^\dagger\otimes I_A$ on a joint vector → Lean represents the vector after the $J_\pi$ density identification and writes the tensor-extended projection directly; reason: unitary change of representation, with the same instances and norm
--   - generalization: the source uses the canonical Borel projection $E_P([1-1/(2t),1))$ → Lean allows any orthogonal projection realizing the same centered slow/fast quadratic-form split, including either allocation of the threshold eigenspace; reason: the canonical source projection is an instance and the stated bound depends only on this split
--   - encoding: the source quantifies over joint vectors in the Hilbert-space representation → Lean explicitly requires the vector field and its projected component to be almost-everywhere strongly measurable; reason: this is the measurability implicit in being a joint vector and excludes Lean's default integral value on nonmeasurable functions
--   - encoding: the source's Markov operator and spectral projection act on $L^2(\pi)$ equivalence classes → Lean represents them by function representatives whose linearity, idempotence, commutation, constant-annihilation, and tensor-extension laws hold almost everywhere; reason: faithful representative-level encoding of the same $L^2$ operators
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), Theorem 3.1, p.24, display (14), proof pp.25-26

import Definitions.Def_QVolKLS_Supplement_GeneralWarmSpectrum

set_option autoImplicit false

namespace QVolKLS.Supplement

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- R. Zhang, arXiv:2610.04987 (held version, sha256 eee7a45e…), **Theorem 3.1
(Slow-spectrum bound from uniform warm-start mixing)**, p.24, display (14), proved on pp.25–26.

For an arbitrary measurable state space, a positive, ergodic, reversible Markov operator with
stationary probability law `pi`, uniform two-warm mixing error `eta` by time `t ≥ 1`, and its
nonstationary spectral projection above `1 - 1/(2t)`, the tensor-extended slow component of every
vector with separable auxiliary Hilbert space has `L²` norm at most an absolute constant times
`eta¹ᐟ⁴` times its homogeneous vector-valued `L⁴` norm.

**Formalization Note.** The vector is represented after the unitary density identification `J_pi`,
so the displayed action is `Pi_slow ⊗ I_A`; this removes `J_pi` and its adjoint from the formula
without changing any instance. Nonintegrable fourth moments have value `+∞`. The predicate
`IsSlowProjection` also covers every orthogonal projection realizing the same slow/fast split,
including either allocation of threshold eigenspace; the paper's canonical projection is one case.
-/
theorem theorem_3_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X : Type) [MeasurableSpace X] (pi : Measure X) [IsProbabilityMeasure pi]
        (P : Kernel X X) [IsMarkovKernel P],
        Kernel.Invariant P pi → Kernel.IsReversible P pi →
        IsPositiveMarkovOperator pi P → IsErgodicMarkovOperator pi P →
        ∀ (eta : ℝ) (t : ℕ), 0 < eta → eta < 1 / 2 → 1 ≤ t →
          GeneralMixTimeTwoLe eta pi P t →
          ∀ S : (X → ℂ) → X → ℂ, IsSlowProjection pi P t S →
            ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
              [TopologicalSpace.SeparableSpace H] (SA : (X → H) → X → H),
              IsTensorExtension pi S SA →
              ∀ Psi : X → H, AEStronglyMeasurable Psi pi →
                AEStronglyMeasurable (SA Psi) pi →
                generalJointL2 pi (SA Psi) ≤
                  ENNReal.ofReal C * ENNReal.ofReal (eta ^ (1 / 4 : ℝ)) * generalJointL4 pi Psi := by sorry

end QVolKLS.Supplement
