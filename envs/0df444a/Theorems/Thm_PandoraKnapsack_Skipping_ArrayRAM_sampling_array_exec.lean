-- Prove2me | Theorems.Thm_PandoraKnapsack_Skipping_ArrayRAM_sampling_array_exec
-- name    : PandoraKnapsack.Skipping.ArrayRAM.sampling_array_exec
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T17:49:40.629132+00:00
-- url     : https://prove2.me/theorems/e99a82db-c670-49f0-8808-87afe708560f
-- title:
--   Pathwise execution and cost of dyadic sampling and policy serialization
-- statement:
--   With correct input dimensions, time labels, column rewards and a solved packing vector in their prescribed tables, the sampling block consumes one uniform draw per item. The choice-time labels are injective and cover the support. The output decodes exactly to the Algorithm 1 skipping list on the computed dyadic plan, including at interval endpoints. Its charged execution cost is at most $(n+m+\mathrm{bitlength}(T)+2)^{24}$.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, Algorithm 1 and Theorem 5.1, Appendix B.1; original machine-implementation lemma for the stated Prove2Me exact coefficient-access model.

import Definitions.Def_PandoraKnapsack_Skipping_SamplingRAM

namespace PandoraKnapsack.Skipping.ArrayRAM

theorem sampling_array_exec {n m T B : ℕ} (I : Instance n m T) (hB : n ≤ B)
    (ω : Fin B → unitInterval) (s : Store)
    (hitems : s.ns 0 = n) (hchoices : s.ns 1 = m) (htimes : s.ns 2 = labelCount T)
    (hcap : s.rs 0 = T)
    (hlabels : ∀ h : Fin (labelCount T), s.tab 0 h.val = timeLabel h)
    (hweights : ∀ c : Fin (columnCount n m T), s.tab 1 c.val = columnWeight I c)
    (hvector : ∀ c : Fin (columnCount n m T),
      s.tab 4 c.val = PandoraPacking.solve (packingRows I) (packingProfits I) c)
    (hdraws : s.draws = 0) :
    Function.Injective (samplingLab m T) ∧
    (∀ (i : Fin n) (j : Fin m) (t : Fin (T+1)), dyadicPlan I i j t.val ≠ 0 →
      ∃ k, samplingLab m T k = (j,t)) ∧
    ∃ v c, Exec I (extendDraws ω) samplingCode s v c ∧
      c ≤ (inputSize n m T+2)^24 ∧ v.draws = n ∧
      ∀ mem : ℤ → ℝ, (∀ r : ℕ, mem r = v.out r) →
        decodeOutput n m mem =
          some (alg1Policy (uniformAssignment hB (samplingLab m T) (dyadicPlan I) ω)) := by sorry

end PandoraKnapsack.Skipping.ArrayRAM
