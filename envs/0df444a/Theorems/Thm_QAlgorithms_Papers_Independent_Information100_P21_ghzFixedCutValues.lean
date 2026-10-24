-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P21_ghzFixedCutValues
-- name    : QAlgorithms.Papers.Independent.Information100.P21.ghzFixedCutValues
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:15:15.330539+00:00
-- url     : https://prove2.me/theorems/7826582a-07b6-4f9d-9f01-f628ab9cc934
-- title:
--   GHZ cut values and local embeddings with Schmidt rank two
-- statement:
--   Let $n\ge2$, and fix a nonempty proper bipartition $S|\bar S$ of the GHZ qubits. Grouping the basis on each side, this state is entangled across the cut and
--   $$R_s^{S|\bar S}(G_n^+)=R_g^{S|\bar S}(G_n^+)=1.$$
--   The cut free set permits entanglement within each side. These values differ from the full-separability standard cost $2^{n-2}$; no biseparable robustness assertion is made.
--
--   For any local dimensions $d_j\ge2$ and local isometries $V_j:\mathbb C^2\to\mathbb C^{d_j}$, construct $\psi=(\bigotimes_jV_j)g_n^+$. Its density operator has fully separable robustnesses $R_g=1$ and $R_s=2^{n-2}$. The coefficient matrix of $\psi$ across each nonempty proper cut has rank two. Thus for $n\ge3$ this is a genuinely multipartite entangled pure separating state. One-dimensional spectator parties are already covered by Lemma X.22.
-- source:
--   The Minimal Dimension of Entangled -Noise Advantage, arXiv:2609.28367v1, PDF p. 3, Main text — GHZ values depend on the free partition

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P21

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arxiv:2609.28367v1, PDF pp.3,30: GHZ cut values and local embeddings.
The paragraph following Theorem X.27 also asserts the fully separable values of
locally embedded GHZ states and Schmidt rank two across every nontrivial cut.
The coefficient matrix below explicitly regroups the constructed embedded ket;
its rank is the Schmidt rank, without assuming entanglement as a hypothesis. -/
theorem ghzFixedCutValues (n : ℕ) (hn : 2≤n) (S : Finset (Fin n))
  (hne : S.Nonempty) (hproper : S≠Finset.univ) :
  QAlgorithms.IsDensityMatrix (cutGHZ n S) ∧ ¬sep (cutGHZ n S) ∧
  rs (cutGHZ n S)=1 ∧ rg (cutGHZ n S)=1 ∧
  (∀ (d : Fin n → ℕ), (∀ j, 2 ≤ d j) →
    ∀ V : (j : Fin n) → Matrix (Fin (d j)) (Fin 2) ℂ,
    (∀ j, (V j)ᴴ * V j = 1) →
    let psi : Vec (Config d) := WithLp.toLp 2
      ((localTensor V).mulVec (fun x => ghzKet n true x))
    let C : Matrix (Side d S) (Side d Sᶜ) ℂ := fun x y =>
      psi (fun j => if hj : j ∈ S then x ⟨j, hj⟩ else y ⟨j, by simp [hj]⟩)
    QAlgorithms.IsDensityMatrix (proj psi) ∧
    fsR d false (proj psi) = 1 ∧ fsR d true (proj psi) = (2 : ℝ)^(n-2) ∧
    Matrix.rank C = 2 ∧
    (3 ≤ n → fsR d false (proj psi) < fsR d true (proj psi))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P21

end
