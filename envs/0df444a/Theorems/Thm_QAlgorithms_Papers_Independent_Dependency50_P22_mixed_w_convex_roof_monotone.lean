-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P22_mixed_w_convex_roof_monotone
-- name    : QAlgorithms.Papers.Independent.Dependency50.P22.mixed_w_convex_roof_monotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:25:13.829146+00:00
-- url     : https://prove2.me/theorems/2c560ef6-fa56-4009-8285-5f84cb13ce4d
-- title:
--   The supported mixed W-class convex roof is an LOCC monotone
-- statement:
--   Fix a party $\star\in\{A,B,C\}$. A normalized pure W-class state is locally unitarily equivalent to $\sqrt{x_0}|000\rangle+\sqrt{x_A}|100\rangle+\sqrt{x_B}|010\rangle+\sqrt{x_C}|001\rangle$, with $x_K\ge0$ and $x_0=1-x_A-x_B-x_C\ge0$, using the canonical boundary conventions of p.13. If $a\ge b$ are the other two canonical weights, define $C_\star=2\sqrt{x_\star a}+\tfrac23 b\sqrt{x_\star/a}$ for $a>0$, and zero for $a=0$.
--
--   For a mixed W-class state $\rho$, take only decompositions supported on this pure domain and define
--   $$
--   \widehat C_\star(\rho)=\min_{\rho=\sum_i p_i|\phi_i\rangle\langle\phi_i|}\sum_i p_i C_\star(\phi_i).
--   $$
--   The weights are nonnegative and sum to one; the pure states are normalized. The minimum is attained. If an LOCC instrument has positive-probability outcomes $j$ with $q_j=\operatorname{Tr}\mathcal E_j(\rho)>0$ and $\rho_j=\mathcal E_j(\rho)/q_j$, then these conditional states remain in the mixed W class and
--   $$
--   \sum_{j:q_j>0}q_j\widehat C_\star(\rho_j)\le\widehat C_\star(\rho).
--   $$
--   The nonnegative expectation is summable for finite or countable labels. This is the convex-roof entanglement monotone needed for mixed W-class transformations.
-- source:
--   Everything You Always Wanted to Know About LOCC (But Were Afraid to Ask), arXiv:1210.4583v2, PDF p. 14, Corollary 4, Eq.(22)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P22

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Dependency50.P22

open QAlgorithms.Papers.Independent.Information100.P27 (Config)

/-- PDF p.14, Corollary 4: the supported convex-roof minimum is attained and is an
LOCC entanglement monotone. Printed: minimize over all pure state decompositions.
Changed: restrict decompositions to the pure W domain of Eq.(20). Why: even I/8
has GHZ decompositions, where that pure cost is undefined; no extension is supplied.
The minimum remains attained, and normalized conditional states are used only
when the branch trace is positive.
This statement uses nonincrease, not the defective unconditional strictness of Lemma 2. -/
theorem mixed_w_convex_roof_monotone (star : Fin 3) :
    (∀ rho, IsMixedW rho → ∃ e : WEnsemble rho, mixedWCost star rho = ensembleWCost star e) ∧
    ∀ rho, IsMixedW rho → ∀ (O : Type*) [Countable O] [DecidableEq O],
      ∀ J : O → Superop (QConfig 3) (QConfig 3),
        InLOCC (fun _ : Fin 3 => 2) J →
        (∀ o (hp : 0 < branchProbability (J o) rho),
          IsMixedW (conditionalOutput (J o) rho hp)) ∧
        Summable (fun o => expectedWCost star (J o) rho) ∧
        (∑' o, expectedWCost star (J o) rho) ≤ mixedWCost star rho := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P22

end
