-- Prove2me | Theorems.Thm_SmoothedPlanted_FFK_claim_49
-- name    : SmoothedPlanted.FFK.claim_49
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:35:06.094789+00:00
-- url     : https://prove2.me/theorems/cba83317-d641-4cf2-a000-0b15d7bf5b49
-- title:
--   Claim 49 — B − δ11ᵀ ⪰ −‖Π‖_op I for B = (J_m − I_m) ⊗ Π
-- statement:
--   For a real matrix $\Pi$ and real $\delta$ satisfying $\Pi\succeq\delta\mathbf1\mathbf1^\top$, define $B=(J_m-I_m)\otimes\Pi$. Then
--   $$B-\delta\mathbf1\mathbf1^\top\succeq-\|\Pi\|_{\rm op}I.$$
--   All matrix orders are positive semidefinite orders, and the norm is the spectral norm.
--
--   Differences from the source:
--   - encoding: finite variables and alphabet → variables and alphabet indexed by Fin n and Fin q; unordered pairs represented by i < j; reason: finite relabelling is bijective and counts every pair once
--   - generalization: Π in [0,1] from the model → arbitrary real Π and real δ satisfying the displayed PSD inequality; reason: the deterministic assertion uses only this PSD inequality and the spectral norm, without requiring δ>0
--   - encoding: Π ⪰ δ11ᵀ and B − δ11ᵀ ⪰ −‖Π‖_op I → Matrix.PosSemidef of Π − δ·J and of B − δ·J + ‖Π‖_op·I, which include symmetry; reason: ⪰ is the Loewner order on symmetric matrices (the paper writes S^n); the hypothesis makes Π symmetric, hence B symmetric
-- source:
--   Kothari, Louis, Paul and Raghavendra, Recovering Planted Subgraphs in Smoothed Models, November 3, 2026, Claim 49, printed p. 32 (PDF p. 34), PDF SHA256 0f9dc5d96e197a1868bf10cade60fcb647db289ebc51985e4d167c942c54f82b

import Definitions.Def_SmoothedPlanted_FFK_Reweighted
import Definitions.Def_SmoothedPlanted_FFK_Certifiable

open scoped BigOperators
open MeasureTheory ProbabilityTheory

noncomputable section

namespace SmoothedPlanted.FFK

theorem claim_49 {m q : ℕ} (Pi : Matrix (Fin q) (Fin q) ℝ) (δ : ℝ)
    (hPi : (Pi - Matrix.of (fun _ _ => δ)).PosSemidef) :
    ((biasedMatrix Pi : Matrix (Fin m × Fin q) (Fin m × Fin q) ℝ) -
      Matrix.of (fun _ _ => δ) + spectralNorm Pi • 1).PosSemidef := by sorry

end SmoothedPlanted.FFK
