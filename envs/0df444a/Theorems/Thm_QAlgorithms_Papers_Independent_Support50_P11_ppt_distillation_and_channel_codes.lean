-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P11_ppt_distillation_and_channel_codes
-- name    : QAlgorithms.Papers.Independent.Support50.P11.ppt_distillation_and_channel_codes
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:09:34.428469+00:00
-- url     : https://prove2.me/theorems/6b1578e1-d4db-472f-a5dd-7e616e9853d6
-- title:
--   Proposition 8: operational PPT distillation and channel codes
-- statement:
--   For a finite CPTP channel $\mathcal N:A'\to B$, let $\nu=N/\dim A'$ be its normalized Choi state, reordered as reference–output. Write $F_\Gamma(\nu,K)$ for the supremum of Bell overlaps obtainable by PPT-preserving CPTP distillation maps, and $D_\Gamma(\nu)$ for the corresponding memoryless vanishing-error rate. Every such map producing Bell overlap $f$ at size $K\ge1$ yields an actual forward-assisted PPTp code with exactly channel fidelity $f$. Thus
--   $$F^{\mathrm{PPTp}}(\mathcal N,K)\ge F_\Gamma(\nu,K),\qquad Q^{\mathrm{PPTp}}(\mathcal N)\ge D_\Gamma(\nu).$$
--   If $\mathcal N$ has an exact single-copy simulation from $\nu$ by local operations and forward classical communication, every PPTp code conversely yields a PPT-preserving distillation map with exactly the same fidelity, and
--   $$F^{\mathrm{PPTp}}(\mathcal N,K)=F_\Gamma(\nu,K),\qquad Q^{\mathrm{PPTp}}(\mathcal N)=D_\Gamma(\nu).$$
--   The transformations use a single channel or a parallel block, retaining the operational meaning of both optima.
-- source:
--   On the power of PPT-preserving and non-signalling codes, arXiv:1406.7142v2, PDF p. 9, Proposition 8: operational PPT distillation and channel codes

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P11

open QAlgorithms.Papers.Independent.Information100.P34 (choi dephasing permutationMatrix)

open QAlgorithms.Papers.Independent.Information100.P21 (pt)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

open QAlgorithms.Papers.Independent.Gap20.P19 (wernerIsometry)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section Statements

variable {I O : Type} [Fintype I] [Nonempty I] [Fintype O] [Nonempty O]

/-- PDF pp.9--10, Proposition 8: fixed-fidelity transformations in both directions
when exact single-copy Choi simulation is available, and both one-shot/quantumCodeCapacity comparisons.
The channel label in printed part (ii) is corrected to the same N as part (i). -/
theorem ppt_distillation_and_channel_codes
    (N : Superop I O) (hN : IsChannel N) :
    (∀ K : ℕ, ∀ hK : 0 < K,
      letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
      (∀ Y : Superop (I × O) (Fin K × Fin K), PPTMap Y →
        ∃ Z : Superop (Fin K × O) (I × Fin K), IsForwardCode K .PPTp Z ∧
          channelFidelity K (link K N Z) =
            effectProb (pureDensity (finiteMaxEntangled (Fin K))) (Y (choiState N))) ∧
      distillFidelity (choiState N) K ≤ optimalCodeFidelity .PPTp N K) ∧
    distillCapacity (choiState N) ≤ quantumCodeCapacity .PPTp N ∧
    (HasChoiSimulation N →
      (∀ K : ℕ, ∀ hK : 0 < K,
        letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
        (∀ Z : Superop (Fin K × O) (I × Fin K), IsForwardCode K .PPTp Z →
          ∃ Y : Superop (I × O) (Fin K × Fin K), PPTMap Y ∧
            effectProb (pureDensity (finiteMaxEntangled (Fin K))) (Y (choiState N)) =
              channelFidelity K (link K N Z)) ∧
        optimalCodeFidelity .PPTp N K = distillFidelity (choiState N) K) ∧
      quantumCodeCapacity .PPTp N = distillCapacity (choiState N)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Support50.P11

end
