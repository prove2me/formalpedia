-- Prove2me | Theorems.Thm_RandomGateDesign_MasterBound_lemma_16
-- name    : RandomGateDesign.MasterBound.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:50.96716+00:00
-- url     : https://prove2.me/theorems/99a394a8-b08f-4ea3-9f43-d76da9be1909
-- title:
--   Lemma 16 and equation (24) — reduction to representation blocks
-- statement:
--   Let $\mu$ be Haar measure and fix a complete decomposition of the mixed tensor representation into nontrivial irreducible blocks $\pi_i$ and a trivial block. For $S\ge1$ gates, the distance of their empirical moment from the Haar moment is the supremum of the norms of the empirical block averages:
--
--   $$\left\|T_{\nu_S,t}-T_{\mu,t}\right\|=\sup_i\left\|\frac1S\sum_{k=1}^{S}\pi_i(U_k)\right\|.$$
--
--   For any probability law on the $S$ gates and any real $\delta$ (with $\delta>0$ when there are no nontrivial blocks), if each block event has probability at most $F_i$, then
--
--   $$\Pr\!\left(\delta(\nu_S,t)\ge\delta\right)\le\sum_i F_i.$$
--
--   This passes from individual block estimates to the full design distance. An empty block family has supremum zero; then the event is empty for $\delta>0$, whereas for $\delta\le0$ it is certain and the empty sum is $0$, which is why $\delta\le0$ is excluded only in that degenerate case.
--
--   **Formalization Note** The source labels blocks by $\lambda\in\Lambda_t$; the statement uses the equivalent intrinsic decomposition, later indexed by $\Lambda_t$ in Fact 9.
-- source:
--   Dulian & Sawicki, Matrix concentration inequalities and efficiency of random universal sets of quantum gates, arXiv:2202.05371v3, p. 20, Lemma 16; p. 12, eq. (24)

import Definitions.Def_RandomGateDesign_MasterBound_Reps

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace RandomGateDesign.MasterBound

theorem lemma_16 {d t r S : ℕ} (μ : Measure (U d))
    (hμ : IsHaarProb μ) (D : MomentDecomposition d t r)
    (hS : 1 ≤ S) (P : Measure (Fin S → U d)) [IsProbabilityMeasure P]
    (δ : ℝ) (hδ : 0 < δ ∨ 0 < r) (F : Fin r → ℝ)
    (hF : ∀ i : Fin r,
      (P {Us | δ ≤ TroppMatrixConcentration.spectralNorm
        ((S : ℂ)⁻¹ • ∑ k : Fin S,
          (D.rep i (Us k) : Matrix (Fin (D.dim i)) (Fin (D.dim i)) ℂ))}).toReal ≤ F i) :
    (∀ Us : Fin S → U d,
      TroppMatrixConcentration.spectralNorm
        (empiricalMoment Us t - momentOp μ t) =
      sSup (Set.range (fun i : Fin r =>
        TroppMatrixConcentration.spectralNorm
          ((S : ℂ)⁻¹ • ∑ k : Fin S,
            (D.rep i (Us k) : Matrix (Fin (D.dim i)) (Fin (D.dim i)) ℂ))))) ∧
    (P {Us | δ ≤ TroppMatrixConcentration.spectralNorm
      (empiricalMoment Us t - momentOp μ t)}).toReal ≤ ∑ i : Fin r, F i := by sorry

end RandomGateDesign.MasterBound
