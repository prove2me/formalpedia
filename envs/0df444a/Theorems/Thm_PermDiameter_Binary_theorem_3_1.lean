-- Prove2me | Theorems.Thm_PermDiameter_Binary_theorem_3_1
-- name    : PermDiameter.Binary.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:11:37.005779+00:00
-- url     : https://prove2.me/theorems/ce6c6dd6-af3b-42d9-a53f-6f28be1b1335
-- title:
--   Theorem 3.1 — a polynomial-time reduction Binary Length $\to$ Binary Diameter with symmetric output and $\langle\Delta\rangle\cong((G_0\times C_{q^2})\wr C_r)\times C_q$
-- statement:
--   There is a polynomial-time computable reduction that maps every instance $(\Sigma_0,g_0,k_0)$ of Binary Length (with $g_0\in G_0=\langle\Sigma_0\rangle$, $k_0$ in binary) to an instance $(\Delta,m)$ of Binary Diameter with $\Delta=\Delta^{-1}$ and
--   $$\ell(g_0,\Sigma_0)\le k_0\iff\operatorname{diam}(\langle\Delta\rangle,\Delta)\le m .$$
--   Moreover, $\langle\Delta\rangle$ is isomorphic to $\big((G_0\times C_{q^2})\wr C_r\big)\times C_q$ for some $q,r\ge1$.
--
--   Together with the PSPACE-hardness of Binary Length this gives the hardness half of Theorem 1.1, already for symmetric generating sets; the isomorphism type transfers hardness to restricted classes of groups.
--
--   **Formalization Note.** The reduction is a map on the subtype of `LengthInstance`s with $g_0\in\langle\Sigma_0\rangle$, computed by a TM2 machine in polynomial time from `encLength` to `encDiam`. $\Delta=\Delta^{-1}$ is "every listed generator's inverse is listed". $C_n$ is `Multiplicative (ZMod n)`, $\wr$ is the wreath product of Definition 2.2 (`Wreath`), and the isomorphism is a `MulEquiv` from the subgroup $\langle\Delta\rangle$.
--
--   Differences from the source:
--   - encoding: instances (Σ, g, k), (Δ, m); "polynomial-time computable reduction" → LengthInstance with g ∈ ⟨Σ⟩ under encLength, DiamInstance under encDiam (image lists, binary numbers), Turing.TM2ComputableInPolyTime; reason: the paper's input format (pp. 3, 10) with an explicit machine model
--   - encoding: Δ = Δ⁻¹ as sets → every listed generator's inverse is listed; reason: equivalent for a finite set given as a list
--   - encoding: permutations compose left to right → Mathlib's Equiv.Perm composes right to left; reason: ℓ and diam are invariant under reversing words, and a group is isomorphic to its opposite, so the iff and the isomorphism type are unchanged
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 12, Theorem 3.1 (proof p. 21)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_PermDiameter_Binary_WordLength
import Definitions.Def_PermDiameter_Binary_Problems
import Definitions.Def_PermDiameter_Binary_Wreath

open Equiv OptimalQueuingComplexity.Restless

namespace PermDiameter.Binary

/-- **Theorem 3.1.** There is a polynomial-time computable reduction mapping every instance
`(Σ₀, g₀, k₀)` of Binary Length (`g₀ ∈ ⟨Σ₀⟩`) to an instance `(Δ, m)` of Binary Diameter with
`Δ = Δ⁻¹` and `ℓ(g₀, Σ₀) ≤ k₀ ⟺ diam(⟨Δ⟩, Δ) ≤ m`; moreover `⟨Δ⟩ ≅ ((G₀ × C_{q²}) ≀ C_r) × C_q`
for some `q, r ≥ 1`, where `G₀ = ⟨Σ₀⟩`. -/
theorem theorem_3_1 :
    ∃ f : {x : LengthInstance // x.Valid} → DiamInstance,
      Nonempty (Turing.TM2ComputableInPolyTime (fun x => encLength x.1) encDiam f) ∧
      ∀ x : {x : LengthInstance // x.Valid},
        (f x).Symmetric ∧ (BinaryLength x.1 ↔ BinaryDiameter (f x)) ∧
        ∃ q r : ℕ, 1 ≤ q ∧ 1 ≤ r ∧
          Nonempty (Subgroup.closure (f x).genSet ≃*
            Wreath (Subgroup.closure x.1.genSet × Multiplicative (ZMod (q ^ 2)))
                (Multiplicative (ZMod r)) × Multiplicative (ZMod q)) := by sorry

end PermDiameter.Binary
