-- Prove2me | Theorems.Thm_SensLabelCover_DH_theorem_3_2
-- name    : SensLabelCover.DH.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:35:27.378521+00:00
-- url     : https://prove2.me/theorems/81ec0e86-07f5-4620-a46b-b294571d5374
-- title:
--   Theorem 3.2 — sensitivity transfer: $\mathrm{SwapSens}(B,\mathcal X)\le C_{\mathcal T}C_{\mathcal R}\,\mathrm{SwapSens}(A,\mathcal Y')+D_{\mathcal R}$
-- statement:
--   Let $\mathcal X$ be a swap-closed family of source instances, and let $\mathcal T$ and $\mathcal R_I$ be a reduction and recovery maps with sensitivity-transfer parameters $(C_{\mathcal T},C_{\mathcal R},D_{\mathcal R})$ on $\mathcal X$. Let $\mathcal Y'$ be a swap-closed family of target instances containing $\mathcal T(\mathcal X)$, let $A$ be an algorithm on $\mathcal Y'$, and let $B$ be the source algorithm with $\mathrm{Law}(B(I))=\mathcal R_I(\mathrm{Law}(A(\mathcal T(I))))$. Then
--   $$\mathrm{SwapSens}(B,\mathcal X)\le C_{\mathcal T}C_{\mathcal R}\,\mathrm{SwapSens}(A,\mathcal Y')+D_{\mathcal R}.$$
--   Consequently, if $C_{\mathcal T}C_{\mathcal R}>0$ and $\mathrm{SwapSens}(B,\mathcal X)\ge L$, then $\mathrm{SwapSens}(A,\mathcal Y')\ge(L-D_{\mathcal R})/(C_{\mathcal T}C_{\mathcal R})$.
--
--   This is the mechanism that carries a sensitivity lower bound from a source problem to a target problem through a reduction.
--
--   Differences from the source:
--   - generalization: Hamming distance on source and target outputs → pseudometric costs $d_X,d_Y$; reason: Hamming distances are pseudometrics, so the statement specializes to both of the paper's uses (2-CSP to Label Cover, Label Cover to Label Cover).
--   - reading: sensitivity-transfer parameters → nonnegative reals; reason: they bound nonnegative quantities.
--   - encoding: maxima in $\mathrm{SwapSens}$ → real suprema (bounded; $0$ on an empty set); algorithms → arbitrary maps from instances to PMFs; reason: same values on the paper's finite families.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 19 (PDF 22), Theorem 3.2

import Mathlib
import Definitions.Def_SensLabelCover_DH_Sensitivity

namespace SensLabelCover.DH

/-- Theorem 3.2 (sensitivity transfer), p. 19 (PDF p. 22). `B(I) := ℛ_I(A(𝒯(I)))`. -/
theorem theorem_3_2 {S T OX OY : Type} [Fintype OX] [Fintype OY]
    (adjS : S → S → Prop) (adjT : T → T → Prop) (dX : OX → OX → ℝ) (dY : OY → OY → ℝ)
    (hdX : IsPseudoCost dX) (hdY : IsPseudoCost dY)
    (𝓧 : Set S) (h𝓧 : SwapClosed adjS 𝓧) (𝒯 : S → T) (ℛ : S → PMF OY → PMF OX)
    (CT CR DR : ℝ) (hpar : IsTransferParams adjS adjT dX dY 𝓧 𝒯 ℛ CT CR DR)
    (𝓨 : Set T) (h𝓨 : SwapClosed adjT 𝓨) (h𝒯𝓨 : ∀ I ∈ 𝓧, 𝒯 I ∈ 𝓨) (A : T → PMF OY) :
    swapSens adjS dX 𝓧 (fun I => ℛ I (A (𝒯 I))) ≤ CT * CR * swapSens adjT dY 𝓨 A + DR ∧
      ∀ L : ℝ, 0 < CT * CR → L ≤ swapSens adjS dX 𝓧 (fun I => ℛ I (A (𝒯 I))) →
        (L - DR) / (CT * CR) ≤ swapSens adjT dY 𝓨 A := by sorry

end SensLabelCover.DH
