-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P01_one_shot_merging
-- name    : QAlgorithms.Papers.Independent.Intake100.P01.one_shot_merging
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:49:47.181679+00:00
-- url     : https://prove2.me/theorems/cbb3773b-e7dd-4595-a351-8446e4bdae7f
-- title:
--   Proposition 4 (One-shot merging)
-- statement:
--   Let $|\psi\rangle_{ABR}$ be a finite-dimensional unit vector, $d=\dim A>0$, and $D>0$ satisfy $\operatorname{Tr}\rho_B^2\le1/D$. For an integer $1\le L\le d$, set $N=\lfloor d/L\rfloor$ and $L'=d-NL<L$. A Haar rotation of a fixed orthogonal decomposition into $N$ rank-$L$ blocks and a residual rank-$L'$ block gives quantum error $Q$ with
--   $$\mathbb E_U Q\le b:=2\sqrt{\frac{L\dim R}{D}}+\frac{2L}{d}.$$
--   There exists such a measurement with $Q\le b$ and a completed merging protocol of entanglement cost $-\log_2L$, squared infidelity at most $b$, and complete-output trace-norm error at most $2\sqrt b$. All blocks map into the same $L$-dimensional Alice output; a zero residual rank gives a zero operator. Both Haar expectation and existence are asserted. This supplies a finite-block merging bound.
-- source:
--   Quantum state merging and negative information, arXiv:quant-ph/0512247v1, PDF p. 6, Proposition 4 (One-shot merging)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P01

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

open QAlgorithms.Papers.Independent.Gap20.P11 (IsLOCC productApply finTransport referenceInformation)

open QAlgorithms.Papers.Independent.Bridge50.P40
  (RankMergingCode OneWayMergingCode mergingFidelity SourceProtocolAchievable)

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRA marginalRB motherTarget motherOutput sourceCopies swap mutualInformation)

open QAlgorithms.Papers.Independent.Information100.P67 (conditionalEntropy)

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open QAlgorithms.Papers.Independent.Advance50.P29 (weakTypicalProjector)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.6,8, Proposition 4: existence AND normalized Haar expectation,
including the rank-L projective decomposition and zero residual branch.
The displayed protocol error is full trace norm; its infidelity is at most (17). -/
theorem one_shot_merging {B R : Type} [Fintype B] [Fintype R]
    [Nonempty B] [Nonempty R] (d L : ℕ) (hd : 0 < d) (hL : 0 < L) (hLd : L ≤ d)
    (psi : EuclideanSpace ℂ (R × (Fin d × B))) (hpsi : IsState psi)
    (D : ℝ) (hD : 0 < D)
    (hpurity : purity (traceLeft (traceLeft (pureDensity psi))) ≤ 1 / D) :
    (∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      IsKrausFamily (randomBlocks d L U) ∧
      ∀ j : Fin (d / L + 1),
        let E := (randomBlocks d L U j)ᴴ * randomBlocks d L U j
        E.IsHermitian ∧ E * E = E ∧
          Matrix.rank E = if j.val < d / L then L else d % L) ∧
    Integrable (fun U => mergingDecouplingError (pureDensity psi) (randomBlocks d L U))
      (Schur.unitaryHaar d) ∧
    (∫ U, mergingDecouplingError (pureDensity psi) (randomBlocks d L U)
      ∂(Schur.unitaryHaar d)) ≤ oneShotBound d L (Fintype.card R) D ∧
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      mergingDecouplingError (pureDensity psi) (randomBlocks d L U) ≤
        oneShotBound d L (Fintype.card R) D ∧
      CompletedMerging (pureDensity psi) (randomBlocks d L U)
        (oneShotBound d L (Fintype.card R) D) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P01

end
